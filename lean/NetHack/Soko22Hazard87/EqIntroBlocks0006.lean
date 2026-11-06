import NetHack.Soko22Hazard87.EqIntroBlocks0005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro1500 (p : Pattern) (selected : d56316 p = 0) : d56543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2110 q = 0) : d53389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2308 q = 0) : d53473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56316 q = 0) : d56543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56316, d56543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56316, d56543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1501 (p : Pattern) (selected : d56317 p = 0) : d56544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2308 q = 0) : d53473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2311 q = 0) : d53476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
    | true =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2312 q = 0) : d53477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2313 q = 0) : d53478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2314 q = 0) : d53479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d53479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2314, d53479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56317 q = 0) : d56544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56317, d56544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56317, d56544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1502 (p : Pattern) (selected : d56321 p = 0) : d56548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2110 q = 0) : d53389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56321 q = 0) : d56548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56321, d56548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56321, d56548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1503 (p : Pattern) (selected : d56326 p = 0) : d56553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56311 q = 0) : d56538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56311, d56538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56311, d56538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1497 q selected
  have h2 (q : Pattern) (selected : d56312 q = 0) : d56539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56312, d56539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56312, d56539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56315 q = 0) : d56542 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56315, d56542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1498 q selected
    | true =>
      simp only [d56315, d56542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1499 q selected
  have h4 (q : Pattern) (selected : d56318 q = 0) : d56545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56318, d56545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1500 q selected
    | true =>
      simp only [d56318, d56545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1501 q selected
  have h5 (q : Pattern) (selected : d56319 q = 0) : d56546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56319, d56546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56319, d56546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56320 q = 0) : d56547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56320, d56547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56320, d56547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56322 q = 0) : d56549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56322, d56549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56322, d56549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1502 q selected
  have h8 (q : Pattern) (selected : d56323 q = 0) : d56550 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56323, d56550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56323, d56550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d56324 q = 0) : d56551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56324, d56551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56324, d56551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56325 q = 0) : d56552 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56325, d56552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56325, d56552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56326 q = 0) : d56553 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56326, d56553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56326, d56553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro1504 (p : Pattern) (selected : d56332 p = 0) : d56559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56327 q = 0) : d56554 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56327, d56554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56327, d56554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1503 q selected
  have h2 (q : Pattern) (selected : d56328 q = 0) : d56555 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56328, d56555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56328, d56555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56329 q = 0) : d56556 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56329, d56556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56329, d56556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56330 q = 0) : d56557 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56330, d56557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56330, d56557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56331 q = 0) : d56558 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56331, d56558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56331, d56558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56332 q = 0) : d56559 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56332, d56559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56332, d56559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1505 (p : Pattern) (selected : d56338 p = 0) : d56565 p = 1 := by
  have h0 (q : Pattern) (selected : d56231 q = 0) : d56458 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56231, d56458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1464 q selected
    | true =>
      simp only [d56231, d56458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1472 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d56255 q = 0) : d56482 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56255, d56482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56255, d56482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1480 q selected
  have h3 (q : Pattern) (selected : d56256 q = 0) : d56483 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56256, d56483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56256, d56483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56280 q = 0) : d56507 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56280, d56507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56280, d56507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1488 q selected
  have h5 (q : Pattern) (selected : d56281 q = 0) : d56508 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56281, d56508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56281, d56508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56282 q = 0) : d56509 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56282, d56509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56282, d56509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56306 q = 0) : d56533 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56306, d56533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56306, d56533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1496 q selected
  have h8 (q : Pattern) (selected : d56307 q = 0) : d56534 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56307, d56534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56307, d56534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56308 q = 0) : d56535 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56308, d56535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56308, d56535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56309 q = 0) : d56536 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56309, d56536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56309, d56536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56333 q = 0) : d56560 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56333, d56560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56333, d56560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1504 q selected
  have h12 (q : Pattern) (selected : d56334 q = 0) : d56561 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56334, d56561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56334, d56561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56335 q = 0) : d56562 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56335, d56562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56335, d56562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56336 q = 0) : d56563 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56336, d56563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56336, d56563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d56337 q = 0) : d56564 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d56337, d56564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56337, d56564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56338 q = 0) : d56565 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d56338, d56565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56338, d56565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1506 (p : Pattern) (selected : d56344 p = 0) : d56571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56339 q = 0) : d56566 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d56339, d56566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1505 q selected
    | true =>
      simp only [d56339, d56566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56340 q = 0) : d56567 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d56340, d56567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56340, d56567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56341 q = 0) : d56568 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d56341, d56568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56341, d56568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56342 q = 0) : d56569 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d56342, d56569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56342, d56569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56343 q = 0) : d56570 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d56343, d56570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56343, d56570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56344 q = 0) : d56571 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d56344, d56571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56344, d56571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1507 (p : Pattern) (selected : d56350 p = 0) : d56577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56345 q = 0) : d56572 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d56345, d56572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1506 q selected
    | true =>
      simp only [d56345, d56572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56346 q = 0) : d56573 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d56346, d56573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56346, d56573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56347 q = 0) : d56574 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d56347, d56574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56347, d56574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56348 q = 0) : d56575 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d56348, d56575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56348, d56575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56349 q = 0) : d56576 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d56349, d56576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56349, d56576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56350 q = 0) : d56577 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d56350, d56577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56350, d56577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1508 (p : Pattern) (selected : d56356 p = 0) : d56583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56351 q = 0) : d56578 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d56351, d56578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1507 q selected
    | true =>
      simp only [d56351, d56578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56352 q = 0) : d56579 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d56352, d56579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56352, d56579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56353 q = 0) : d56580 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d56353, d56580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56353, d56580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56354 q = 0) : d56581 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d56354, d56581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56354, d56581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56355 q = 0) : d56582 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d56355, d56582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56355, d56582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56356 q = 0) : d56583 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d56356, d56583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56356, d56583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1509 (p : Pattern) (selected : d56362 p = 0) : d56589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56357 q = 0) : d56584 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d56357, d56584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1508 q selected
    | true =>
      simp only [d56357, d56584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56358 q = 0) : d56585 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d56358, d56585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56358, d56585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56359 q = 0) : d56586 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d56359, d56586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56359, d56586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56360 q = 0) : d56587 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d56360, d56587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56360, d56587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56361 q = 0) : d56588 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d56361, d56588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56361, d56588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56362 q = 0) : d56589 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d56362, d56589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56362, d56589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1510 (p : Pattern) (selected : d56368 p = 0) : d56595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56363 q = 0) : d56590 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d56363, d56590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1509 q selected
    | true =>
      simp only [d56363, d56590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56364 q = 0) : d56591 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d56364, d56591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56364, d56591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56365 q = 0) : d56592 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d56365, d56592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56365, d56592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56366 q = 0) : d56593 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d56366, d56593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56366, d56593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56367 q = 0) : d56594 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d56367, d56594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56367, d56594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56368 q = 0) : d56595 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d56368, d56595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56368, d56595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1511 (p : Pattern) (selected : d56374 p = 0) : d56601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56369 q = 0) : d56596 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d56369, d56596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1510 q selected
    | true =>
      simp only [d56369, d56596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56370 q = 0) : d56597 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d56370, d56597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56370, d56597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56371 q = 0) : d56598 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d56371, d56598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56371, d56598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56372 q = 0) : d56599 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d56372, d56599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56372, d56599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56373 q = 0) : d56600 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d56373, d56600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56373, d56600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56374 q = 0) : d56601 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d56374, d56601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56374, d56601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1512 (p : Pattern) (selected : d56380 p = 0) : d56607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56375 q = 0) : d56602 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56375, d56602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1511 q selected
    | true =>
      simp only [d56375, d56602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56376 q = 0) : d56603 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56376, d56603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56376, d56603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56377 q = 0) : d56604 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56377, d56604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56377, d56604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56378 q = 0) : d56605 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56378, d56605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56378, d56605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56379 q = 0) : d56606 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56379, d56606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56379, d56606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56380 q = 0) : d56607 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56380, d56607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56380, d56607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1513 (p : Pattern) (selected : d56168 p = 1) : d56608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d190 q = 1) : d4336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191 q = 1) : d51641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56168 q = 1) : d56608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56168, d56608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56168, d56608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1514 (p : Pattern) (selected : d56169 p = 1) : d56609 p = 1 := by
  have h0 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d190 q = 1) : d4336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191 q = 1) : d51641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d202 q = 1) : d202 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d204 q = 1) : d204 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d207 q = 1) : d4340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d208 q = 1) : d4341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208, d4341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d208, d4341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d209 q = 1) : d51644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209, d51644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d209, d51644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d56169 q = 1) : d56609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56169, d56609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56169, d56609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1515 (p : Pattern) (selected : d56179 p = 1) : d56614 p = 1 := by
  have h0 (q : Pattern) (selected : d56167 q = 1) : d56167 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56170 q = 1) : d56610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56170, d56610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1513 q selected
    | true =>
      simp only [d56170, d56610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1514 q selected
  have h2 (q : Pattern) (selected : d56172 q = 1) : d56172 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56173 q = 1) : d56611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56173, d56611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56173, d56611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56174 q = 1) : d56612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56174, d56612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56174, d56612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56177 q = 1) : d56177 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56178 q = 1) : d56613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56178, d56613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56178, d56613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56179 q = 1) : d56614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56179, d56614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56179, d56614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1516 (p : Pattern) (selected : d56188 p = 1) : d56620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d306 q = 1) : d306 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371 q = 1) : d371 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d372 q = 1) : d4372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d373 q = 1) : d51658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56188 q = 1) : d56620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56188, d56620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56188, d56620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1517 (p : Pattern) (selected : d56189 p = 1) : d56621 p = 1 := by
  have h0 (q : Pattern) (selected : d306 q = 1) : d306 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h3 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371 q = 1) : d371 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372 q = 1) : d4372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d373 q = 1) : d51658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d384 q = 1) : d384 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d386 q = 1) : d386 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d388 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20 q selected
    | true =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h10 (q : Pattern) (selected : d389 q = 1) : d4376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d391 q = 1) : d391 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d392 q = 1) : d4377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d392, d4377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d392, d4377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d393 q = 1) : d51661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d393, d51661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d393, d51661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56189 q = 1) : d56621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56189, d56621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56189, d56621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1518 (p : Pattern) (selected : d56201 p = 1) : d56626 p = 1 := by
  have h0 (q : Pattern) (selected : d56187 q = 1) : d56187 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56190 q = 1) : d56622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56190, d56622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1516 q selected
    | true =>
      simp only [d56190, d56622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1517 q selected
  have h2 (q : Pattern) (selected : d56193 q = 1) : d56193 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56194 q = 1) : d56623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56194, d56623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56194, d56623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56195 q = 1) : d56624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56195, d56624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56195, d56624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56199 q = 1) : d56199 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56200 q = 1) : d56625 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56200, d56625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56200, d56625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56201 q = 1) : d56626 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56201, d56626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56201, d56626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1519 (p : Pattern) (selected : d56207 p = 1) : d56632 p = 1 := by
  have h0 (q : Pattern) (selected : d56164 q = 1) : d56164 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d56180 q = 1) : d56615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56180, d56615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56180, d56615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1515 q selected
  have h3 (q : Pattern) (selected : d56181 q = 1) : d56616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56181, d56616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56181, d56616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56182 q = 1) : d56617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56182, d56617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56182, d56617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56183 q = 1) : d56618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56183, d56618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56183, d56618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56184 q = 1) : d56619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56184, d56619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56184, d56619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56202 q = 1) : d56627 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56202, d56627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56202, d56627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1518 q selected
  have h8 (q : Pattern) (selected : d56203 q = 1) : d56628 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56203, d56628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56203, d56628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56204 q = 1) : d56629 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56204, d56629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56204, d56629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56205 q = 1) : d56630 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56205, d56630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56205, d56630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56206 q = 1) : d56631 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56206, d56631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56206, d56631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d56207 q = 1) : d56632 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56207, d56632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56207, d56632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1520 (p : Pattern) (selected : d56211 p = 1) : d56633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d527 q = 1) : d527 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d604 q = 1) : d604 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d605 q = 1) : d4409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d606 q = 1) : d51683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56211 q = 1) : d56633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56211, d56633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56211, d56633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1521 (p : Pattern) (selected : d56212 p = 1) : d56634 p = 1 := by
  have h0 (q : Pattern) (selected : d527 q = 1) : d527 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h3 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d604 q = 1) : d604 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d605 q = 1) : d4409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d606 q = 1) : d51683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d619 q = 1) : d619 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d621 q = 1) : d621 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37 q selected
    | true =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h10 (q : Pattern) (selected : d625 q = 1) : d4413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d627 q = 1) : d627 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d628 q = 1) : d4414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d628, d4414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d628, d4414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d629 q = 1) : d51686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d629, d51686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d629, d51686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56212 q = 1) : d56634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56212, d56634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56212, d56634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1522 (p : Pattern) (selected : d56224 p = 1) : d56639 p = 1 := by
  have h0 (q : Pattern) (selected : d56210 q = 1) : d56210 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56213 q = 1) : d56635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56213, d56635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1520 q selected
    | true =>
      simp only [d56213, d56635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1521 q selected
  have h2 (q : Pattern) (selected : d56216 q = 1) : d56216 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56217 q = 1) : d56636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56217, d56636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56217, d56636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56218 q = 1) : d56637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56218, d56637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56218, d56637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56222 q = 1) : d56222 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56223 q = 1) : d56638 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56223, d56638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56223, d56638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56224 q = 1) : d56639 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56224, d56639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56224, d56639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1523 (p : Pattern) (selected : d56230 p = 1) : d56645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56225 q = 1) : d56640 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56225, d56640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56225, d56640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1522 q selected
  have h2 (q : Pattern) (selected : d56226 q = 1) : d56641 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56226, d56641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56226, d56641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56227 q = 1) : d56642 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56227, d56642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56227, d56642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56228 q = 1) : d56643 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56228, d56643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56228, d56643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56229 q = 1) : d56644 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56229, d56644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56229, d56644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56230 q = 1) : d56645 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56230, d56645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56230, d56645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1524 (p : Pattern) (selected : d56235 p = 1) : d56647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d819 q = 1) : d819 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d910 q = 1) : d910 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d911 q = 1) : d4447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d912 q = 1) : d51709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56235 q = 1) : d56647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56235, d56647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56235, d56647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1525 (p : Pattern) (selected : d56236 p = 1) : d56648 p = 1 := by
  have h0 (q : Pattern) (selected : d819 q = 1) : d819 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h3 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d910 q = 1) : d910 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d911 q = 1) : d4447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d912 q = 1) : d51709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d925 q = 1) : d925 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d927 q = 1) : d927 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro61 q selected
    | true =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h10 (q : Pattern) (selected : d931 q = 1) : d4451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d933 q = 1) : d933 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d934 q = 1) : d4452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d934, d4452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d934, d4452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d935 q = 1) : d51712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d935, d51712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d935, d51712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56236 q = 1) : d56648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56236, d56648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56236, d56648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1526 (p : Pattern) (selected : d56248 p = 1) : d56653 p = 1 := by
  have h0 (q : Pattern) (selected : d56234 q = 1) : d56234 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56237 q = 1) : d56649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56237, d56649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1524 q selected
    | true =>
      simp only [d56237, d56649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1525 q selected
  have h2 (q : Pattern) (selected : d56240 q = 1) : d56240 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56241 q = 1) : d56650 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56241, d56650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56241, d56650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56242 q = 1) : d56651 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56242, d56651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56242, d56651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56246 q = 1) : d56246 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56247 q = 1) : d56652 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56247, d56652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56247, d56652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56248 q = 1) : d56653 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56248, d56653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56248, d56653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1527 (p : Pattern) (selected : d56254 p = 1) : d56659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56249 q = 1) : d56654 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56249, d56654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56249, d56654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1526 q selected
  have h2 (q : Pattern) (selected : d56250 q = 1) : d56655 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56250, d56655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56250, d56655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56251 q = 1) : d56656 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56251, d56656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56251, d56656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56252 q = 1) : d56657 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56252, d56657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56252, d56657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56253 q = 1) : d56658 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56253, d56658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56253, d56658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56254 q = 1) : d56659 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56254, d56659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56254, d56659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1528 (p : Pattern) (selected : d56260 p = 1) : d56662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1198 q = 1) : d1198 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1321 q = 1) : d1321 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1322 q = 1) : d4486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1323 q = 1) : d51736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56260 q = 1) : d56662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56260, d56662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56260, d56662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1529 (p : Pattern) (selected : d56261 p = 1) : d56663 p = 1 := by
  have h0 (q : Pattern) (selected : d1198 q = 1) : d1198 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h3 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1321 q = 1) : d1321 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d1322 q = 1) : d4486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1323 q = 1) : d51736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1336 q = 1) : d1336 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d1338 q = 1) : d1338 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d1341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro91 q selected
    | true =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h10 (q : Pattern) (selected : d1342 q = 1) : d4490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1344 q = 1) : d1344 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1345 q = 1) : d4491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1345, d4491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1345, d4491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1346 q = 1) : d51739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1346, d51739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1346, d51739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56261 q = 1) : d56663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56261, d56663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56261, d56663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1530 (p : Pattern) (selected : d56273 p = 1) : d56668 p = 1 := by
  have h0 (q : Pattern) (selected : d56259 q = 1) : d56259 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56262 q = 1) : d56664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56262, d56664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1528 q selected
    | true =>
      simp only [d56262, d56664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1529 q selected
  have h2 (q : Pattern) (selected : d56265 q = 1) : d56265 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56266 q = 1) : d56665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56266, d56665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56266, d56665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56267 q = 1) : d56666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56267, d56666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56267, d56666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56271 q = 1) : d56271 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56272 q = 1) : d56667 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56272, d56667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56272, d56667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56273 q = 1) : d56668 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56273, d56668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56273, d56668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1531 (p : Pattern) (selected : d56279 p = 1) : d56674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56274 q = 1) : d56669 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56274, d56669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56274, d56669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1530 q selected
  have h2 (q : Pattern) (selected : d56275 q = 1) : d56670 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56275, d56670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56275, d56670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56276 q = 1) : d56671 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56276, d56671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56276, d56671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56277 q = 1) : d56672 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56277, d56672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56277, d56672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56278 q = 1) : d56673 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56278, d56673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56278, d56673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56279 q = 1) : d56674 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56279, d56674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56279, d56674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1532 (p : Pattern) (selected : d56286 p = 1) : d56678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1659 q = 1) : d1659 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1798 q = 1) : d1798 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1799 q = 1) : d4526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1800 q = 1) : d51764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56286 q = 1) : d56678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56286, d56678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56286, d56678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1533 (p : Pattern) (selected : d56287 p = 1) : d56679 p = 1 := by
  have h0 (q : Pattern) (selected : d1659 q = 1) : d1659 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h3 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1798 q = 1) : d1798 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d1799 q = 1) : d4526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1800 q = 1) : d51764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1813 q = 1) : d1813 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d1815 q = 1) : d1815 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d1818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro127 q selected
    | true =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h10 (q : Pattern) (selected : d1819 q = 1) : d4530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1821 q = 1) : d1821 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1822 q = 1) : d4531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1822, d4531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1822, d4531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1823 q = 1) : d51767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1823, d51767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1823, d51767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56287 q = 1) : d56679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56287, d56679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56287, d56679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1534 (p : Pattern) (selected : d56299 p = 1) : d56684 p = 1 := by
  have h0 (q : Pattern) (selected : d56285 q = 1) : d56285 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56288 q = 1) : d56680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56288, d56680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1532 q selected
    | true =>
      simp only [d56288, d56680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1533 q selected
  have h2 (q : Pattern) (selected : d56291 q = 1) : d56291 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56292 q = 1) : d56681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56292, d56681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56292, d56681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56293 q = 1) : d56682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56293, d56682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56293, d56682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56297 q = 1) : d56297 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56298 q = 1) : d56683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56298, d56683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56298, d56683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56299 q = 1) : d56684 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56299, d56684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56299, d56684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1535 (p : Pattern) (selected : d56305 p = 1) : d56690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56300 q = 1) : d56685 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56300, d56685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56300, d56685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1534 q selected
  have h2 (q : Pattern) (selected : d56301 q = 1) : d56686 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56301, d56686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56301, d56686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56302 q = 1) : d56687 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56302, d56687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56302, d56687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56303 q = 1) : d56688 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56303, d56688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56303, d56688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56304 q = 1) : d56689 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56304, d56689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56304, d56689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56305 q = 1) : d56690 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56305, d56690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56305, d56690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1536 (p : Pattern) (selected : d56313 p = 1) : d56695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2142 q = 1) : d2142 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2276 q = 1) : d2276 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d2277 q = 1) : d4567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2278 q = 1) : d51793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56313 q = 1) : d56695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56313, d56695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56313, d56695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1537 (p : Pattern) (selected : d56314 p = 1) : d56696 p = 1 := by
  have h0 (q : Pattern) (selected : d2142 q = 1) : d2142 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h3 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2276 q = 1) : d2276 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d2277 q = 1) : d4567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2278 q = 1) : d51793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2291 q = 1) : d2291 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d2293 q = 1) : d2293 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d2296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro164 q selected
    | true =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h10 (q : Pattern) (selected : d2297 q = 1) : d4571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2299 q = 1) : d2299 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d2300 q = 1) : d4572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2300, d4572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2300, d4572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2301 q = 1) : d51796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2301, d51796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2301, d51796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56314 q = 1) : d56696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56314, d56696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56314, d56696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1538 (p : Pattern) (selected : d56326 p = 1) : d56701 p = 1 := by
  have h0 (q : Pattern) (selected : d56312 q = 1) : d56312 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56315 q = 1) : d56697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56315, d56697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1536 q selected
    | true =>
      simp only [d56315, d56697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1537 q selected
  have h2 (q : Pattern) (selected : d56318 q = 1) : d56318 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56319 q = 1) : d56698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56319, d56698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56319, d56698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56320 q = 1) : d56699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56320, d56699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56320, d56699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56324 q = 1) : d56324 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d56325 q = 1) : d56700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56325, d56700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56325, d56700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56326 q = 1) : d56701 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56326, d56701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56326, d56701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1539 (p : Pattern) (selected : d56332 p = 1) : d56707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56327 q = 1) : d56702 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56327, d56702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56327, d56702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1538 q selected
  have h2 (q : Pattern) (selected : d56328 q = 1) : d56703 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56328, d56703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56328, d56703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56329 q = 1) : d56704 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56329, d56704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56329, d56704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56330 q = 1) : d56705 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56330, d56705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56330, d56705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56331 q = 1) : d56706 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56331, d56706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56331, d56706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56332 q = 1) : d56707 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56332, d56707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56332, d56707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1540 (p : Pattern) (selected : d56338 p = 1) : d56713 p = 1 := by
  have h0 (q : Pattern) (selected : d56231 q = 1) : d56646 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56231, d56646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1519 q selected
    | true =>
      simp only [d56231, d56646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1523 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d56255 q = 1) : d56660 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56255, d56660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56255, d56660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1527 q selected
  have h3 (q : Pattern) (selected : d56256 q = 1) : d56661 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56256, d56661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56256, d56661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56280 q = 1) : d56675 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56280, d56675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56280, d56675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1531 q selected
  have h5 (q : Pattern) (selected : d56281 q = 1) : d56676 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56281, d56676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56281, d56676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56282 q = 1) : d56677 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56282, d56677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56282, d56677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56306 q = 1) : d56691 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56306, d56691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56306, d56691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1535 q selected
  have h8 (q : Pattern) (selected : d56307 q = 1) : d56692 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56307, d56692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56307, d56692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56308 q = 1) : d56693 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56308, d56693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56308, d56693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56309 q = 1) : d56694 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56309, d56694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56309, d56694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56333 q = 1) : d56708 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56333, d56708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56333, d56708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1539 q selected
  have h12 (q : Pattern) (selected : d56334 q = 1) : d56709 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56334, d56709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56334, d56709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56335 q = 1) : d56710 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56335, d56710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56335, d56710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56336 q = 1) : d56711 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56336, d56711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56336, d56711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d56337 q = 1) : d56712 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d56337, d56712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56337, d56712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56338 q = 1) : d56713 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d56338, d56713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56338, d56713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1541 (p : Pattern) (selected : d56344 p = 1) : d56719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56339 q = 1) : d56714 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d56339, d56714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1540 q selected
    | true =>
      simp only [d56339, d56714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56340 q = 1) : d56715 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d56340, d56715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56340, d56715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56341 q = 1) : d56716 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d56341, d56716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56341, d56716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56342 q = 1) : d56717 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d56342, d56717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56342, d56717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56343 q = 1) : d56718 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d56343, d56718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56343, d56718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56344 q = 1) : d56719 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d56344, d56719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56344, d56719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1542 (p : Pattern) (selected : d56350 p = 1) : d56725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56345 q = 1) : d56720 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d56345, d56720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1541 q selected
    | true =>
      simp only [d56345, d56720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56346 q = 1) : d56721 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d56346, d56721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56346, d56721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56347 q = 1) : d56722 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d56347, d56722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56347, d56722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56348 q = 1) : d56723 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d56348, d56723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56348, d56723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56349 q = 1) : d56724 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d56349, d56724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56349, d56724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56350 q = 1) : d56725 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d56350, d56725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56350, d56725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1543 (p : Pattern) (selected : d56356 p = 1) : d56731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56351 q = 1) : d56726 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d56351, d56726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1542 q selected
    | true =>
      simp only [d56351, d56726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56352 q = 1) : d56727 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d56352, d56727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56352, d56727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56353 q = 1) : d56728 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d56353, d56728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56353, d56728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56354 q = 1) : d56729 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d56354, d56729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56354, d56729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56355 q = 1) : d56730 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d56355, d56730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56355, d56730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56356 q = 1) : d56731 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d56356, d56731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56356, d56731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1544 (p : Pattern) (selected : d56362 p = 1) : d56737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56357 q = 1) : d56732 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d56357, d56732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1543 q selected
    | true =>
      simp only [d56357, d56732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56358 q = 1) : d56733 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d56358, d56733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56358, d56733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56359 q = 1) : d56734 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d56359, d56734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56359, d56734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56360 q = 1) : d56735 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d56360, d56735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56360, d56735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56361 q = 1) : d56736 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d56361, d56736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56361, d56736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56362 q = 1) : d56737 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d56362, d56737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56362, d56737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1545 (p : Pattern) (selected : d56368 p = 1) : d56743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56363 q = 1) : d56738 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d56363, d56738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1544 q selected
    | true =>
      simp only [d56363, d56738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56364 q = 1) : d56739 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d56364, d56739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56364, d56739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56365 q = 1) : d56740 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d56365, d56740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56365, d56740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56366 q = 1) : d56741 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d56366, d56741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56366, d56741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56367 q = 1) : d56742 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d56367, d56742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56367, d56742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56368 q = 1) : d56743 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d56368, d56743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56368, d56743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1546 (p : Pattern) (selected : d56374 p = 1) : d56749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56369 q = 1) : d56744 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d56369, d56744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1545 q selected
    | true =>
      simp only [d56369, d56744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56370 q = 1) : d56745 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d56370, d56745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56370, d56745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56371 q = 1) : d56746 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d56371, d56746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56371, d56746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56372 q = 1) : d56747 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d56372, d56747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56372, d56747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56373 q = 1) : d56748 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d56373, d56748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56373, d56748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56374 q = 1) : d56749 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d56374, d56749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56374, d56749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1547 (p : Pattern) (selected : d56380 p = 1) : d56755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56375 q = 1) : d56750 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56375, d56750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1546 q selected
    | true =>
      simp only [d56375, d56750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d56376 q = 1) : d56751 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56376, d56751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56376, d56751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56377 q = 1) : d56752 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56377, d56752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56377, d56752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56378 q = 1) : d56753 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56378, d56753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56378, d56753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56379 q = 1) : d56754 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56379, d56754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56379, d56754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56380 q = 1) : d56755 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56380, d56755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56380, d56755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1548 (p : Pattern) (selected : d56778 p = 0) : d57086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45 q = 0) : d51897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56777 q = 0) : d57085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56777, d57085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56777, d57085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56778 q = 0) : d57086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56778, d57086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56778, d57086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1549 (p : Pattern) (selected : d56780 p = 0) : d57088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45 q = 0) : d51897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56777 q = 0) : d57085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56777, d57085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56777, d57085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d52 q = 0) : d51904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d51904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d52, d51904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56779 q = 0) : d57087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56779, d57087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56779, d57087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56780 q = 0) : d57088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56780, d57088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56780, d57088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1550 (p : Pattern) (selected : d56786 p = 0) : d57094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56781 q = 0) : d57089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56781, d57089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1548 q selected
    | true =>
      simp only [d56781, d57089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1549 q selected
  have h2 (q : Pattern) (selected : d56782 q = 0) : d57090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56782, d57090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56782, d57090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56783 q = 0) : d57091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56783, d57091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56783, d57091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56784 q = 0) : d57092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56784, d57092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56784, d57092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56785 q = 0) : d57093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56785, d57093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56785, d57093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d56786 q = 0) : d57094 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56786, d57094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56786, d57094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1551 (p : Pattern) (selected : d56792 p = 0) : d57100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56791 q = 0) : d57099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56792 q = 0) : d57100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56792, d57100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56792, d57100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1552 (p : Pattern) (selected : d56796 p = 0) : d57104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56791 q = 0) : d57099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d107 q = 0) : d51959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d51959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d107, d51959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d108 q = 0) : d51960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d51960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d108, d51960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56795 q = 0) : d57103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56795, d57103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56795, d57103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56796 q = 0) : d57104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56796, d57104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56796, d57104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1553 (p : Pattern) (selected : d56801 p = 0) : d57109 p = 1 := by
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
  have h4 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h5 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189 q = 0) : d52009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190 q = 0) : d52010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56800 q = 0) : d57108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56800, d57108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56800, d57108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56801 q = 0) : d57109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56801, d57109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56801, d57109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1554 (p : Pattern) (selected : d56803 p = 0) : d57111 p = 1 := by
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
  have h4 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h5 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189 q = 0) : d52009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190 q = 0) : d52010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56800 q = 0) : d57108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56800, d57108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56800, d57108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h15 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d207 q = 0) : d52025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d208 q = 0) : d52026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208, d52026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d208, d52026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56802 q = 0) : d57110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56802, d57110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56802, d57110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56803 q = 0) : d57111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56803, d57111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56803, d57111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1555 (p : Pattern) (selected : d56805 p = 0) : d57113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56791 q = 0) : d57099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56805 q = 0) : d57113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56805, d57113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56805, d57113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1556 (p : Pattern) (selected : d56815 p = 0) : d57123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56793 q = 0) : d57101 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56793, d57101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56793, d57101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1551 q selected
  have h2 (q : Pattern) (selected : d56794 q = 0) : d57102 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56794, d57102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56794, d57102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56797 q = 0) : d57105 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56797, d57105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1551 q selected
    | true =>
      simp only [d56797, d57105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1552 q selected
  have h4 (q : Pattern) (selected : d56798 q = 0) : d57106 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56798, d57106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56798, d57106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56799 q = 0) : d57107 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56799, d57107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56799, d57107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56804 q = 0) : d57112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56804, d57112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1553 q selected
    | true =>
      simp only [d56804, d57112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1554 q selected
  have h7 (q : Pattern) (selected : d56806 q = 0) : d57114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56806, d57114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1555 q selected
    | true =>
      simp only [d56806, d57114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56807 q = 0) : d57115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56807, d57115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56807, d57115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56808 q = 0) : d57116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56808, d57116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56808, d57116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56809 q = 0) : d57117 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56809, d57117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56809, d57117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56810 q = 0) : d57118 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56810, d57118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56810, d57118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1555 q selected
  have h12 (q : Pattern) (selected : d56811 q = 0) : d57119 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56811, d57119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56811, d57119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56812 q = 0) : d57120 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56812, d57120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56812, d57120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56813 q = 0) : d57121 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56813, d57121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56813, d57121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56814 q = 0) : d57122 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56814, d57122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56814, d57122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56815 q = 0) : d57123 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56815, d57123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56815, d57123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1557 (p : Pattern) (selected : d56822 p = 0) : d57130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d280 q = 0) : d52079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d281 q = 0) : d52080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56821 q = 0) : d57129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56822 q = 0) : d57130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56822, d57130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56822, d57130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1558 (p : Pattern) (selected : d56826 p = 0) : d57134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d280 q = 0) : d52079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d281 q = 0) : d52080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56821 q = 0) : d57129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h6 (q : Pattern) (selected : d287 q = 0) : d52086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d52086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d287, d52086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d288 q = 0) : d52087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d52087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d288, d52087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56825 q = 0) : d57133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56825, d57133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56825, d57133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56826 q = 0) : d57134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56826, d57134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56826, d57134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1559 (p : Pattern) (selected : d56831 p = 0) : d57139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d297 q = 0) : d52096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro232 q selected
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d298 q = 0) : d52097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 0) : d52098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h5 (q : Pattern) (selected : d368 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro243 q selected
    | true =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h6 (q : Pattern) (selected : d369 q = 0) : d52137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372 q = 0) : d52140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56830 q = 0) : d57138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56830, d57138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56830, d57138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56831 q = 0) : d57139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56831, d57139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56831, d57139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1560 (p : Pattern) (selected : d56833 p = 0) : d57141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d297 q = 0) : d52096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro232 q selected
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d298 q = 0) : d52097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 0) : d52098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h5 (q : Pattern) (selected : d368 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro243 q selected
    | true =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h6 (q : Pattern) (selected : d369 q = 0) : d52137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d372 q = 0) : d52140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56830 q = 0) : d57138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56830, d57138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56830, d57138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d377 q = 0) : d52145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro245 q selected
    | true =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h12 (q : Pattern) (selected : d378 q = 0) : d52146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d379 q = 0) : d52147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d386 q = 0) : d52154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro247 q selected
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
  have h15 (q : Pattern) (selected : d388 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro248 q selected
    | true =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h16 (q : Pattern) (selected : d389 q = 0) : d52155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d390 q = 0) : d52156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d391 q = 0) : d52157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d392 q = 0) : d52158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d392, d52158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d392, d52158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56832 q = 0) : d57140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56832, d57140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56832, d57140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56833 q = 0) : d57141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56833, d57141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56833, d57141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1561 (p : Pattern) (selected : d56835 p = 0) : d57143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d280 q = 0) : d52079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d281 q = 0) : d52080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56821 q = 0) : d57129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56791 q = 0) : d57099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56791, d57099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56835 q = 0) : d57143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56835, d57143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56835, d57143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1562 (p : Pattern) (selected : d56840 p = 0) : d57148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d280 q = 0) : d52079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d281 q = 0) : d52080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56821 q = 0) : d57129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56821, d57129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56840 q = 0) : d57148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56840, d57148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56840, d57148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1563 (p : Pattern) (selected : d56846 p = 0) : d57154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56823 q = 0) : d57131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56823, d57131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56823, d57131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1557 q selected
  have h2 (q : Pattern) (selected : d56824 q = 0) : d57132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56824, d57132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56824, d57132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56827 q = 0) : d57135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56827, d57135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1557 q selected
    | true =>
      simp only [d56827, d57135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1558 q selected
  have h4 (q : Pattern) (selected : d56828 q = 0) : d57136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56828, d57136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56828, d57136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56829 q = 0) : d57137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56829, d57137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56829, d57137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56834 q = 0) : d57142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56834, d57142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1559 q selected
    | true =>
      simp only [d56834, d57142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1560 q selected
  have h7 (q : Pattern) (selected : d56836 q = 0) : d57144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56836, d57144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1561 q selected
    | true =>
      simp only [d56836, d57144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1552 q selected
  have h8 (q : Pattern) (selected : d56837 q = 0) : d57145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56837, d57145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56837, d57145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56838 q = 0) : d57146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56838, d57146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56838, d57146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56839 q = 0) : d57147 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56839, d57147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56839, d57147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56841 q = 0) : d57149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56841, d57149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56841, d57149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1562 q selected
  have h12 (q : Pattern) (selected : d56842 q = 0) : d57150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56842, d57150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56842, d57150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56843 q = 0) : d57151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56843, d57151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56843, d57151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56844 q = 0) : d57152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56844, d57152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56844, d57152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56845 q = 0) : d57153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56845, d57153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56845, d57153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56846 q = 0) : d57154 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56846, d57154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56846, d57154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1564 (p : Pattern) (selected : d56852 p = 0) : d57160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56787 q = 0) : d57095 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56787, d57095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56787, d57095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1550 q selected
  have h2 (q : Pattern) (selected : d56788 q = 0) : d57096 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56788, d57096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56788, d57096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56789 q = 0) : d57097 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56789, d57097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56789, d57097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56790 q = 0) : d57098 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56790, d57098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56790, d57098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56816 q = 0) : d57124 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56816, d57124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56816, d57124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1556 q selected
  have h6 (q : Pattern) (selected : d56817 q = 0) : d57125 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56817, d57125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56817, d57125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56818 q = 0) : d57126 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56818, d57126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56818, d57126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56819 q = 0) : d57127 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56819, d57127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56819, d57127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56820 q = 0) : d57128 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56820, d57128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56820, d57128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56847 q = 0) : d57155 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56847, d57155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56847, d57155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1563 q selected
  have h11 (q : Pattern) (selected : d56848 q = 0) : d57156 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56848, d57156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56848, d57156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d56849 q = 0) : d57157 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56849, d57157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56849, d57157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56850 q = 0) : d57158 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56850, d57158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56850, d57158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56851 q = 0) : d57159 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56851, d57159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56851, d57159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d56852 q = 0) : d57160 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56852, d57160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d56852, d57160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1565 (p : Pattern) (selected : d56854 p = 0) : d57162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d492 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d493 q = 0) : d52240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d494 q = 0) : d52241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56853 q = 0) : d57161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56854 q = 0) : d57162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56854, d57162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56854, d57162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1566 (p : Pattern) (selected : d56858 p = 0) : d57166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d492 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d493 q = 0) : d52240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d494 q = 0) : d52241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56853 q = 0) : d57161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d502 q = 0) : d52249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d502, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro269 q selected
  have h6 (q : Pattern) (selected : d503 q = 0) : d52250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d52250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d503, d52250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d504 q = 0) : d52251 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d52251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d504, d52251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56857 q = 0) : d57165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56857, d57165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56857, d57165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56858 q = 0) : d57166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56858, d57166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56858, d57166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1567 (p : Pattern) (selected : d56863 p = 0) : d57171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d515 q = 0) : d52262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro271 q selected
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d516 q = 0) : d52263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 0) : d52264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h5 (q : Pattern) (selected : d601 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro286 q selected
    | true =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h6 (q : Pattern) (selected : d602 q = 0) : d52309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d605 q = 0) : d52312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56862 q = 0) : d57170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56862, d57170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56862, d57170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56863 q = 0) : d57171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56863, d57171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56863, d57171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1568 (p : Pattern) (selected : d56865 p = 0) : d57173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d515 q = 0) : d52262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro271 q selected
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d516 q = 0) : d52263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 0) : d52264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h5 (q : Pattern) (selected : d601 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro286 q selected
    | true =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h6 (q : Pattern) (selected : d602 q = 0) : d52309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d605 q = 0) : d52312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56862 q = 0) : d57170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56862, d57170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56862, d57170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d611 q = 0) : d52318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d52318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro289 q selected
    | true =>
      simp only [d611, d52318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro290 q selected
  have h12 (q : Pattern) (selected : d612 q = 0) : d52319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d52319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d612, d52319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d613 q = 0) : d52320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d52320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d613, d52320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d621 q = 0) : d52328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro293 q selected
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
  have h15 (q : Pattern) (selected : d624 q = 0) : d52249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro294 q selected
    | true =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h16 (q : Pattern) (selected : d625 q = 0) : d52329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d626 q = 0) : d52330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d627 q = 0) : d52331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d628 q = 0) : d52332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d628, d52332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d628, d52332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56864 q = 0) : d57172 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56864, d57172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56864, d57172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56865 q = 0) : d57173 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56865, d57173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56865, d57173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1569 (p : Pattern) (selected : d56868 p = 0) : d57176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d492 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d493 q = 0) : d52240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d494 q = 0) : d52241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56853 q = 0) : d57161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d633 q = 0) : d52337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d634 q = 0) : d52338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d635 q = 0) : d52339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56867 q = 0) : d57175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56867, d57175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56867, d57175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56868 q = 0) : d57176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56868, d57176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56868, d57176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1570 (p : Pattern) (selected : d56870 p = 0) : d57178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d633 q = 0) : d52337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d634 q = 0) : d52338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d635 q = 0) : d52339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56867 q = 0) : d57175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56867, d57175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56867, d57175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d639 q = 0) : d52343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d52343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro269 q selected
    | true =>
      simp only [d639, d52343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d640 q = 0) : d52344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d52344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d640, d52344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d641 q = 0) : d52345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d52345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d641, d52345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56869 q = 0) : d57177 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56869, d57177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56869, d57177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56870 q = 0) : d57178 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56870, d57178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56870, d57178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1571 (p : Pattern) (selected : d56875 p = 0) : d57183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d492 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d493 q = 0) : d52240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d494 q = 0) : d52241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56853 q = 0) : d57161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56853, d57161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56875 q = 0) : d57183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56875, d57183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56875, d57183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1572 (p : Pattern) (selected : d56881 p = 0) : d57189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56855 q = 0) : d57163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56855, d57163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56855, d57163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1565 q selected
  have h2 (q : Pattern) (selected : d56856 q = 0) : d57164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56856, d57164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56856, d57164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56859 q = 0) : d57167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56859, d57167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1565 q selected
    | true =>
      simp only [d56859, d57167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1566 q selected
  have h4 (q : Pattern) (selected : d56860 q = 0) : d57168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56860, d57168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56860, d57168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56861 q = 0) : d57169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56861, d57169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56861, d57169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56866 q = 0) : d57174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56866, d57174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1567 q selected
    | true =>
      simp only [d56866, d57174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1568 q selected
  have h7 (q : Pattern) (selected : d56871 q = 0) : d57179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56871, d57179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1569 q selected
    | true =>
      simp only [d56871, d57179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1570 q selected
  have h8 (q : Pattern) (selected : d56872 q = 0) : d57180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56872, d57180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56872, d57180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56873 q = 0) : d57181 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56873, d57181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56873, d57181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56874 q = 0) : d57182 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56874, d57182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56874, d57182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56876 q = 0) : d57184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56876, d57184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56876, d57184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1571 q selected
  have h12 (q : Pattern) (selected : d56877 q = 0) : d57185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56877, d57185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56877, d57185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56878 q = 0) : d57186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56878, d57186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56878, d57186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56879 q = 0) : d57187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56879, d57187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56879, d57187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56880 q = 0) : d57188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56880, d57188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56880, d57188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56881 q = 0) : d57189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56881, d57189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56881, d57189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1573 (p : Pattern) (selected : d56887 p = 0) : d57195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56882 q = 0) : d57190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56882, d57190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56882, d57190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1572 q selected
  have h2 (q : Pattern) (selected : d56883 q = 0) : d57191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56883, d57191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56883, d57191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56884 q = 0) : d57192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56884, d57192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56884, d57192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56885 q = 0) : d57193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56885, d57193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56885, d57193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56886 q = 0) : d57194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56886, d57194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56886, d57194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56887 q = 0) : d57195 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56887, d57195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56887, d57195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1574 (p : Pattern) (selected : d56890 p = 0) : d57198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d784 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d785 q = 0) : d52462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d786 q = 0) : d52463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56889 q = 0) : d57197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56890 q = 0) : d57198 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56890, d57198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56890, d57198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1575 (p : Pattern) (selected : d56894 p = 0) : d57202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d784 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d785 q = 0) : d52462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d786 q = 0) : d52463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56889 q = 0) : d57197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d794 q = 0) : d52471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d794, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro327 q selected
  have h6 (q : Pattern) (selected : d795 q = 0) : d52472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d52472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d795, d52472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d796 q = 0) : d52473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d52473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d796, d52473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56893 q = 0) : d57201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56893, d57201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56893, d57201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56894 q = 0) : d57202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56894, d57202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56894, d57202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1576 (p : Pattern) (selected : d56899 p = 0) : d57207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d807 q = 0) : d52484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro329 q selected
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d808 q = 0) : d52485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 0) : d52486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h5 (q : Pattern) (selected : d907 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro348 q selected
    | true =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h6 (q : Pattern) (selected : d908 q = 0) : d52530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d911 q = 0) : d52533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56898 q = 0) : d57206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56898, d57206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56898, d57206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56899 q = 0) : d57207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56899, d57207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56899, d57207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1577 (p : Pattern) (selected : d56901 p = 0) : d57209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d807 q = 0) : d52484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro329 q selected
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d808 q = 0) : d52485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 0) : d52486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h5 (q : Pattern) (selected : d907 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro348 q selected
    | true =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h6 (q : Pattern) (selected : d908 q = 0) : d52530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d911 q = 0) : d52533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56898 q = 0) : d57206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56898, d57206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56898, d57206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d917 q = 0) : d52539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d52539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro351 q selected
    | true =>
      simp only [d917, d52539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro352 q selected
  have h12 (q : Pattern) (selected : d918 q = 0) : d52540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d52540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d918, d52540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d919 q = 0) : d52541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d52541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d919, d52541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d927 q = 0) : d52549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro355 q selected
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
  have h15 (q : Pattern) (selected : d930 q = 0) : d52471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro356 q selected
    | true =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h16 (q : Pattern) (selected : d931 q = 0) : d52550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d932 q = 0) : d52551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d933 q = 0) : d52552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d934 q = 0) : d52553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d934, d52553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d934, d52553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56900 q = 0) : d57208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56900, d57208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56900, d57208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56901 q = 0) : d57209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56901, d57209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56901, d57209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1578 (p : Pattern) (selected : d56904 p = 0) : d57212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d784 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d785 q = 0) : d52462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d786 q = 0) : d52463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56889 q = 0) : d57197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d939 q = 0) : d52558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d940 q = 0) : d52559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d941 q = 0) : d52560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56903 q = 0) : d57211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56903, d57211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56903, d57211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56904 q = 0) : d57212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56904, d57212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56904, d57212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1579 (p : Pattern) (selected : d56906 p = 0) : d57214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d939 q = 0) : d52558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d940 q = 0) : d52559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d941 q = 0) : d52560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56903 q = 0) : d57211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56903, d57211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56903, d57211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d945 q = 0) : d52564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d52564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro327 q selected
    | true =>
      simp only [d945, d52564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d946 q = 0) : d52565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d52565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d946, d52565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d947 q = 0) : d52566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d52566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d947, d52566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56905 q = 0) : d57213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56905, d57213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56905, d57213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56906 q = 0) : d57214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56906, d57214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56906, d57214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1580 (p : Pattern) (selected : d56911 p = 0) : d57219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d784 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d785 q = 0) : d52462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d786 q = 0) : d52463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56889 q = 0) : d57197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56889, d57197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56911 q = 0) : d57219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56911, d57219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56911, d57219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1581 (p : Pattern) (selected : d56917 p = 0) : d57225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56891 q = 0) : d57199 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56891, d57199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56891, d57199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1574 q selected
  have h2 (q : Pattern) (selected : d56892 q = 0) : d57200 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56892, d57200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56892, d57200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56895 q = 0) : d57203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56895, d57203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1574 q selected
    | true =>
      simp only [d56895, d57203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1575 q selected
  have h4 (q : Pattern) (selected : d56896 q = 0) : d57204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56896, d57204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56896, d57204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56897 q = 0) : d57205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56897, d57205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56897, d57205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56902 q = 0) : d57210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56902, d57210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1576 q selected
    | true =>
      simp only [d56902, d57210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1577 q selected
  have h7 (q : Pattern) (selected : d56907 q = 0) : d57215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56907, d57215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1578 q selected
    | true =>
      simp only [d56907, d57215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1579 q selected
  have h8 (q : Pattern) (selected : d56908 q = 0) : d57216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56908, d57216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56908, d57216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56909 q = 0) : d57217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56909, d57217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56909, d57217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56910 q = 0) : d57218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56910, d57218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56910, d57218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56912 q = 0) : d57220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56912, d57220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56912, d57220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1580 q selected
  have h12 (q : Pattern) (selected : d56913 q = 0) : d57221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56913, d57221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56913, d57221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56914 q = 0) : d57222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56914, d57222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56914, d57222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56915 q = 0) : d57223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56915, d57223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56915, d57223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56916 q = 0) : d57224 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56916, d57224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56916, d57224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56917 q = 0) : d57225 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56917, d57225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56917, d57225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1582 (p : Pattern) (selected : d56923 p = 0) : d57231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56918 q = 0) : d57226 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56918, d57226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56918, d57226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1581 q selected
  have h2 (q : Pattern) (selected : d56919 q = 0) : d57227 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56919, d57227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56919, d57227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56920 q = 0) : d57228 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56920, d57228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56920, d57228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56921 q = 0) : d57229 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56921, d57229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56921, d57229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56922 q = 0) : d57230 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56922, d57230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56922, d57230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56923 q = 0) : d57231 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56923, d57231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56923, d57231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1583 (p : Pattern) (selected : d56927 p = 0) : d57235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1163 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d1164 q = 0) : d52745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1165 q = 0) : d52746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56926 q = 0) : d57234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56927 q = 0) : d57235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56927, d57235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56927, d57235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1584 (p : Pattern) (selected : d56931 p = 0) : d57239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1163 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d1164 q = 0) : d52745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1165 q = 0) : d52746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56926 q = 0) : d57234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1173 q = 0) : d52754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1173, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro399 q selected
  have h6 (q : Pattern) (selected : d1174 q = 0) : d52755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d52755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1174, d52755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1175 q = 0) : d52756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d52756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1175, d52756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56930 q = 0) : d57238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56930, d57238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56930, d57238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56931 q = 0) : d57239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56931, d57239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56931, d57239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1585 (p : Pattern) (selected : d56936 p = 0) : d57244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1186 q = 0) : d52767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro401 q selected
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d1187 q = 0) : d52768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 0) : d52769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h5 (q : Pattern) (selected : d1318 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro424 q selected
    | true =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h6 (q : Pattern) (selected : d1319 q = 0) : d52810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1322 q = 0) : d52813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56935 q = 0) : d57243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56935, d57243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56935, d57243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56936 q = 0) : d57244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56936, d57244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56936, d57244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1586 (p : Pattern) (selected : d56938 p = 0) : d57246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1186 q = 0) : d52767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro401 q selected
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d1187 q = 0) : d52768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 0) : d52769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h5 (q : Pattern) (selected : d1318 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro424 q selected
    | true =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h6 (q : Pattern) (selected : d1319 q = 0) : d52810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1322 q = 0) : d52813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56935 q = 0) : d57243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56935, d57243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56935, d57243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1328 q = 0) : d52819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro427 q selected
    | true =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro428 q selected
  have h12 (q : Pattern) (selected : d1329 q = 0) : d52820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1330 q = 0) : d52821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d1338 q = 0) : d52829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro431 q selected
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
  have h15 (q : Pattern) (selected : d1341 q = 0) : d52754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro432 q selected
    | true =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h16 (q : Pattern) (selected : d1342 q = 0) : d52830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d1343 q = 0) : d52831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d1344 q = 0) : d52832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d1345 q = 0) : d52833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1345, d52833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d1345, d52833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56937 q = 0) : d57245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56937, d57245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56937, d57245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56938 q = 0) : d57246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56938, d57246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56938, d57246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1587 (p : Pattern) (selected : d56941 p = 0) : d57249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1163 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d1164 q = 0) : d52745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1165 q = 0) : d52746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56926 q = 0) : d57234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1350 q = 0) : d52838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1351 q = 0) : d52839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1352 q = 0) : d52840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56940 q = 0) : d57248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56940, d57248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56940, d57248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56941 q = 0) : d57249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56941, d57249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56941, d57249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1588 (p : Pattern) (selected : d56943 p = 0) : d57251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1350 q = 0) : d52838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1351 q = 0) : d52839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1352 q = 0) : d52840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56940 q = 0) : d57248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56940, d57248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56940, d57248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1356 q = 0) : d52844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d52844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro399 q selected
    | true =>
      simp only [d1356, d52844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1357 q = 0) : d52845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d52845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1357, d52845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1358 q = 0) : d52846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d52846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1358, d52846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56942 q = 0) : d57250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56942, d57250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56942, d57250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56943 q = 0) : d57251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56943, d57251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56943, d57251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1589 (p : Pattern) (selected : d56948 p = 0) : d57256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1163 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d1164 q = 0) : d52745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1165 q = 0) : d52746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56926 q = 0) : d57234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56926, d57234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56948 q = 0) : d57256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56948, d57256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56948, d57256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1590 (p : Pattern) (selected : d56954 p = 0) : d57262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56928 q = 0) : d57236 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56928, d57236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56928, d57236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1583 q selected
  have h2 (q : Pattern) (selected : d56929 q = 0) : d57237 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56929, d57237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56929, d57237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56932 q = 0) : d57240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56932, d57240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1583 q selected
    | true =>
      simp only [d56932, d57240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1584 q selected
  have h4 (q : Pattern) (selected : d56933 q = 0) : d57241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56933, d57241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56933, d57241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56934 q = 0) : d57242 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56934, d57242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56934, d57242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56939 q = 0) : d57247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56939, d57247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1585 q selected
    | true =>
      simp only [d56939, d57247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1586 q selected
  have h7 (q : Pattern) (selected : d56944 q = 0) : d57252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56944, d57252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1587 q selected
    | true =>
      simp only [d56944, d57252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1588 q selected
  have h8 (q : Pattern) (selected : d56945 q = 0) : d57253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56945, d57253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56945, d57253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56946 q = 0) : d57254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56946, d57254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56946, d57254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56947 q = 0) : d57255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56947, d57255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56947, d57255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56949 q = 0) : d57257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56949, d57257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56949, d57257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1589 q selected
  have h12 (q : Pattern) (selected : d56950 q = 0) : d57258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56950, d57258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56950, d57258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56951 q = 0) : d57259 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56951, d57259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56951, d57259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56952 q = 0) : d57260 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56952, d57260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56952, d57260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56953 q = 0) : d57261 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56953, d57261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56953, d57261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56954 q = 0) : d57262 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56954, d57262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56954, d57262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1591 (p : Pattern) (selected : d56960 p = 0) : d57268 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56955 q = 0) : d57263 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56955, d57263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56955, d57263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1590 q selected
  have h2 (q : Pattern) (selected : d56956 q = 0) : d57264 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56956, d57264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56956, d57264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56957 q = 0) : d57265 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56957, d57265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56957, d57265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56958 q = 0) : d57266 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56958, d57266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56958, d57266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56959 q = 0) : d57267 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56959, d57267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56959, d57267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56960 q = 0) : d57268 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56960, d57268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56960, d57268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1592 (p : Pattern) (selected : d56965 p = 0) : d57273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1624 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d1625 q = 0) : d53066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1626 q = 0) : d53067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56964 q = 0) : d57272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56965 q = 0) : d57273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56965, d57273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56965, d57273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1593 (p : Pattern) (selected : d56969 p = 0) : d57277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1624 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d1625 q = 0) : d53066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1626 q = 0) : d53067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56964 q = 0) : d57272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1634 q = 0) : d53075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1634, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro481 q selected
  have h6 (q : Pattern) (selected : d1635 q = 0) : d53076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d53076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1635, d53076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1636 q = 0) : d53077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d53077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1636, d53077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56968 q = 0) : d57276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56968, d57276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56968, d57276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56969 q = 0) : d57277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56969, d57277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56969, d57277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1594 (p : Pattern) (selected : d56974 p = 0) : d57282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1647 q = 0) : d53088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro483 q selected
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d1648 q = 0) : d53089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 0) : d53090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h5 (q : Pattern) (selected : d1795 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro510 q selected
    | true =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h6 (q : Pattern) (selected : d1796 q = 0) : d53125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1799 q = 0) : d53128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56973 q = 0) : d57281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56973, d57281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56973, d57281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56974 q = 0) : d57282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56974, d57282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56974, d57282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1595 (p : Pattern) (selected : d56976 p = 0) : d57284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1647 q = 0) : d53088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro483 q selected
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d1648 q = 0) : d53089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 0) : d53090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h5 (q : Pattern) (selected : d1795 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro510 q selected
    | true =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h6 (q : Pattern) (selected : d1796 q = 0) : d53125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1799 q = 0) : d53128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56973 q = 0) : d57281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56973, d57281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56973, d57281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1805 q = 0) : d53134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro513 q selected
    | true =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro514 q selected
  have h12 (q : Pattern) (selected : d1806 q = 0) : d53135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1807 q = 0) : d53136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d1815 q = 0) : d53144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro517 q selected
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
  have h15 (q : Pattern) (selected : d1818 q = 0) : d53075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro518 q selected
    | true =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h16 (q : Pattern) (selected : d1819 q = 0) : d53145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d1820 q = 0) : d53146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d1821 q = 0) : d53147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d1822 q = 0) : d53148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1822, d53148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d1822, d53148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d56975 q = 0) : d57283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56975, d57283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56975, d57283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d56976 q = 0) : d57284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56976, d57284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56976, d57284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1596 (p : Pattern) (selected : d56979 p = 0) : d57287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1624 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d1625 q = 0) : d53066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1626 q = 0) : d53067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56964 q = 0) : d57272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1827 q = 0) : d53153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1828 q = 0) : d53154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1829 q = 0) : d53155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56978 q = 0) : d57286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56978, d57286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56978, d57286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56979 q = 0) : d57287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56979, d57287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56979, d57287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1597 (p : Pattern) (selected : d56981 p = 0) : d57289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1827 q = 0) : d53153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1828 q = 0) : d53154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1829 q = 0) : d53155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56978 q = 0) : d57286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56978, d57286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56978, d57286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1833 q = 0) : d53159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d53159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro481 q selected
    | true =>
      simp only [d1833, d53159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1834 q = 0) : d53160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d53160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1834, d53160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1835 q = 0) : d53161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d53161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1835, d53161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d56980 q = 0) : d57288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56980, d57288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56980, d57288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56981 q = 0) : d57289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56981, d57289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56981, d57289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1598 (p : Pattern) (selected : d56986 p = 0) : d57294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1624 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d1625 q = 0) : d53066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1626 q = 0) : d53067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d56964 q = 0) : d57272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56964, d57272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56986 q = 0) : d57294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56986, d57294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d56986, d57294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1599 (p : Pattern) (selected : d56992 p = 0) : d57300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56966 q = 0) : d57274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56966, d57274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56966, d57274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1592 q selected
  have h2 (q : Pattern) (selected : d56967 q = 0) : d57275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56967, d57275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56967, d57275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d56970 q = 0) : d57278 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56970, d57278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1592 q selected
    | true =>
      simp only [d56970, d57278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1593 q selected
  have h4 (q : Pattern) (selected : d56971 q = 0) : d57279 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56971, d57279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56971, d57279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d56972 q = 0) : d57280 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56972, d57280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d56972, d57280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56977 q = 0) : d57285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56977, d57285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1594 q selected
    | true =>
      simp only [d56977, d57285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1595 q selected
  have h7 (q : Pattern) (selected : d56982 q = 0) : d57290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56982, d57290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1596 q selected
    | true =>
      simp only [d56982, d57290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1597 q selected
  have h8 (q : Pattern) (selected : d56983 q = 0) : d57291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56983, d57291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56983, d57291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56984 q = 0) : d57292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56984, d57292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56984, d57292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d56985 q = 0) : d57293 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56985, d57293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d56985, d57293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56987 q = 0) : d57295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56987, d57295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56987, d57295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1598 q selected
  have h12 (q : Pattern) (selected : d56988 q = 0) : d57296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56988, d57296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d56988, d57296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d56989 q = 0) : d57297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56989, d57297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d56989, d57297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d56990 q = 0) : d57298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56990, d57298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d56990, d57298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d56991 q = 0) : d57299 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56991, d57299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d56991, d57299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d56992 q = 0) : d57300 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56992, d57300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d56992, d57300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1600 (p : Pattern) (selected : d56998 p = 0) : d57306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d56993 q = 0) : d57301 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56993, d57301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56993, d57301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1599 q selected
  have h2 (q : Pattern) (selected : d56994 q = 0) : d57302 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56994, d57302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56994, d57302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56995 q = 0) : d57303 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56995, d57303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56995, d57303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56996 q = 0) : d57304 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56996, d57304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56996, d57304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56997 q = 0) : d57305 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56997, d57305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56997, d57305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56998 q = 0) : d57306 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56998, d57306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56998, d57306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1601 (p : Pattern) (selected : d57004 p = 0) : d57312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57003 q = 0) : d57311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57004 q = 0) : d57312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57004, d57312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57004, d57312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1602 (p : Pattern) (selected : d57008 p = 0) : d57316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57003 q = 0) : d57311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2117 q = 0) : d53396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2117, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
  have h6 (q : Pattern) (selected : d2118 q = 0) : d53397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d53397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2118, d53397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2119 q = 0) : d53398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d53398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2119, d53398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57007 q = 0) : d57315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57007, d57315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57007, d57315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57008 q = 0) : d57316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57008, d57316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57008, d57316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1603 (p : Pattern) (selected : d57013 p = 0) : d57321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2130 q = 0) : d53409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro572 q selected
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d2131 q = 0) : d53410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 0) : d53411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h5 (q : Pattern) (selected : d2273 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro600 q selected
    | true =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h6 (q : Pattern) (selected : d2274 q = 0) : d53442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2277 q = 0) : d53445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57012 q = 0) : d57320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57012, d57320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57012, d57320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57013 q = 0) : d57321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57013, d57321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57013, d57321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1604 (p : Pattern) (selected : d57015 p = 0) : d57323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2130 q = 0) : d53409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro572 q selected
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d2131 q = 0) : d53410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 0) : d53411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h5 (q : Pattern) (selected : d2273 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro600 q selected
    | true =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h6 (q : Pattern) (selected : d2274 q = 0) : d53442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2277 q = 0) : d53445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57012 q = 0) : d57320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57012, d57320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57012, d57320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2283 q = 0) : d53451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro603 q selected
    | true =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro604 q selected
  have h12 (q : Pattern) (selected : d2284 q = 0) : d53452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2285 q = 0) : d53453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d2293 q = 0) : d53461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro607 q selected
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
  have h15 (q : Pattern) (selected : d2296 q = 0) : d53396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro608 q selected
    | true =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h16 (q : Pattern) (selected : d2297 q = 0) : d53462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2298 q = 0) : d53463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d2299 q = 0) : d53464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d2300 q = 0) : d53465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2300, d53465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2300, d53465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d57014 q = 0) : d57322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57014, d57322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57014, d57322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d57015 q = 0) : d57323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57015, d57323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57015, d57323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro1605 (p : Pattern) (selected : d57018 p = 0) : d57326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57003 q = 0) : d57311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57017 q = 0) : d57325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57017, d57325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57017, d57325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57018 q = 0) : d57326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57018, d57326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57018, d57326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1606 (p : Pattern) (selected : d57020 p = 0) : d57328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57017 q = 0) : d57325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57017, d57325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57017, d57325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2311 q = 0) : d53476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
    | true =>
      simp only [d2311, d53476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2312 q = 0) : d53477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2312, d53477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2313 q = 0) : d53478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2313, d53478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57019 q = 0) : d57327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57019, d57327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57019, d57327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57020 q = 0) : d57328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57020, d57328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57020, d57328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1607 (p : Pattern) (selected : d57025 p = 0) : d57333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2107 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d2108 q = 0) : d53387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2109 q = 0) : d53388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57003 q = 0) : d57311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57003, d57311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57025 q = 0) : d57333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57025, d57333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57025, d57333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1608 (p : Pattern) (selected : d57031 p = 0) : d57339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57005 q = 0) : d57313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57005, d57313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57005, d57313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1601 q selected
  have h2 (q : Pattern) (selected : d57006 q = 0) : d57314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57006, d57314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57006, d57314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57009 q = 0) : d57317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57009, d57317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1601 q selected
    | true =>
      simp only [d57009, d57317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1602 q selected
  have h4 (q : Pattern) (selected : d57010 q = 0) : d57318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57010, d57318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57010, d57318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57011 q = 0) : d57319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57011, d57319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57011, d57319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57016 q = 0) : d57324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57016, d57324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1603 q selected
    | true =>
      simp only [d57016, d57324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1604 q selected
  have h7 (q : Pattern) (selected : d57021 q = 0) : d57329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57021, d57329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1605 q selected
    | true =>
      simp only [d57021, d57329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1606 q selected
  have h8 (q : Pattern) (selected : d57022 q = 0) : d57330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57022, d57330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57022, d57330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57023 q = 0) : d57331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57023, d57331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d57023, d57331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d57024 q = 0) : d57332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57024, d57332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57024, d57332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57026 q = 0) : d57334 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57026, d57334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57026, d57334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1607 q selected
  have h12 (q : Pattern) (selected : d57027 q = 0) : d57335 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57027, d57335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57027, d57335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57028 q = 0) : d57336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57028, d57336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57028, d57336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57029 q = 0) : d57337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57029, d57337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57029, d57337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57030 q = 0) : d57338 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57030, d57338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57030, d57338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d57031 q = 0) : d57339 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57031, d57339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d57031, d57339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1609 (p : Pattern) (selected : d57037 p = 0) : d57345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57032 q = 0) : d57340 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57032, d57340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57032, d57340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1608 q selected
  have h2 (q : Pattern) (selected : d57033 q = 0) : d57341 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57033, d57341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57033, d57341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57034 q = 0) : d57342 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57034, d57342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57034, d57342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57035 q = 0) : d57343 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57035, d57343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57035, d57343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57036 q = 0) : d57344 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57036, d57344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57036, d57344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57037 q = 0) : d57345 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57037, d57345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57037, d57345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1610 (p : Pattern) (selected : d57043 p = 0) : d57351 p = 1 := by
  have h0 (q : Pattern) (selected : d56888 q = 0) : d57196 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56888, d57196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1564 q selected
    | true =>
      simp only [d56888, d57196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1573 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d56924 q = 0) : d57232 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56924, d57232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56924, d57232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1582 q selected
  have h3 (q : Pattern) (selected : d56925 q = 0) : d57233 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56925, d57233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56925, d57233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56961 q = 0) : d57269 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56961, d57269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56961, d57269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1591 q selected
  have h5 (q : Pattern) (selected : d56962 q = 0) : d57270 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56962, d57270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56962, d57270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56963 q = 0) : d57271 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56963, d57271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56963, d57271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56999 q = 0) : d57307 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56999, d57307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56999, d57307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1600 q selected
  have h8 (q : Pattern) (selected : d57000 q = 0) : d57308 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57000, d57308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57000, d57308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57001 q = 0) : d57309 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57001, d57309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57001, d57309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57002 q = 0) : d57310 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57002, d57310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57002, d57310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57038 q = 0) : d57346 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57038, d57346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57038, d57346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1609 q selected
  have h12 (q : Pattern) (selected : d57039 q = 0) : d57347 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57039, d57347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57039, d57347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d57040 q = 0) : d57348 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57040, d57348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57040, d57348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d57041 q = 0) : d57349 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57041, d57349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57041, d57349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d57042 q = 0) : d57350 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d57042, d57350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57042, d57350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d57043 q = 0) : d57351 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d57043, d57351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d57043, d57351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1611 (p : Pattern) (selected : d57049 p = 0) : d57357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57044 q = 0) : d57352 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d57044, d57352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1610 q selected
    | true =>
      simp only [d57044, d57352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57045 q = 0) : d57353 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d57045, d57353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57045, d57353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57046 q = 0) : d57354 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d57046, d57354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57046, d57354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57047 q = 0) : d57355 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d57047, d57355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57047, d57355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57048 q = 0) : d57356 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d57048, d57356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57048, d57356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57049 q = 0) : d57357 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d57049, d57357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57049, d57357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1612 (p : Pattern) (selected : d57055 p = 0) : d57363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57050 q = 0) : d57358 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d57050, d57358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1611 q selected
    | true =>
      simp only [d57050, d57358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57051 q = 0) : d57359 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d57051, d57359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57051, d57359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57052 q = 0) : d57360 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d57052, d57360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57052, d57360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57053 q = 0) : d57361 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d57053, d57361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57053, d57361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57054 q = 0) : d57362 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d57054, d57362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57054, d57362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57055 q = 0) : d57363 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d57055, d57363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57055, d57363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1613 (p : Pattern) (selected : d57061 p = 0) : d57369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57056 q = 0) : d57364 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d57056, d57364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1612 q selected
    | true =>
      simp only [d57056, d57364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57057 q = 0) : d57365 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d57057, d57365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57057, d57365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57058 q = 0) : d57366 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d57058, d57366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57058, d57366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57059 q = 0) : d57367 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d57059, d57367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57059, d57367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57060 q = 0) : d57368 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d57060, d57368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57060, d57368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57061 q = 0) : d57369 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d57061, d57369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57061, d57369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1614 (p : Pattern) (selected : d57067 p = 0) : d57375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57062 q = 0) : d57370 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d57062, d57370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1613 q selected
    | true =>
      simp only [d57062, d57370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57063 q = 0) : d57371 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d57063, d57371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57063, d57371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57064 q = 0) : d57372 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d57064, d57372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57064, d57372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57065 q = 0) : d57373 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d57065, d57373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57065, d57373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57066 q = 0) : d57374 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d57066, d57374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57066, d57374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57067 q = 0) : d57375 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d57067, d57375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57067, d57375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1615 (p : Pattern) (selected : d57073 p = 0) : d57381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57068 q = 0) : d57376 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d57068, d57376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1614 q selected
    | true =>
      simp only [d57068, d57376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57069 q = 0) : d57377 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d57069, d57377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57069, d57377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57070 q = 0) : d57378 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d57070, d57378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57070, d57378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57071 q = 0) : d57379 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d57071, d57379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57071, d57379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57072 q = 0) : d57380 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d57072, d57380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57072, d57380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57073 q = 0) : d57381 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d57073, d57381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57073, d57381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1616 (p : Pattern) (selected : d57078 p = 0) : d57386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57074 q = 0) : d57382 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d57074, d57382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1615 q selected
    | true =>
      simp only [d57074, d57382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57075 q = 0) : d57383 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d57075, d57383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57075, d57383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57076 q = 0) : d57384 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d57076, d57384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57076, d57384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57077 q = 0) : d57385 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d57077, d57385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57077, d57385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57078 q = 0) : d57386 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d57078, d57386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57078, d57386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1617 (p : Pattern) (selected : d57084 p = 0) : d57392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57079 q = 0) : d57387 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d57079, d57387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1616 q selected
    | true =>
      simp only [d57079, d57387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57080 q = 0) : d57388 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d57080, d57388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57080, d57388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57081 q = 0) : d57389 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d57081, d57389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57081, d57389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57082 q = 0) : d57390 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d57082, d57390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57082, d57390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57083 q = 0) : d57391 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d57083, d57391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57083, d57391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57084 q = 0) : d57392 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d57084, d57392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57084, d57392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1618 (p : Pattern) (selected : d56801 p = 1) : d57394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d119 q = 1) : d119 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d190 q = 1) : d4336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56800 q = 1) : d57393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56800, d57393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56800, d57393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56801 q = 1) : d57394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56801, d57394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56801, d57394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1619 (p : Pattern) (selected : d56803 p = 1) : d57396 p = 1 := by
  have h0 (q : Pattern) (selected : d119 q = 1) : d119 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d190 q = 1) : d4336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56800 q = 1) : d57393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56800, d57393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56800, d57393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d197 q = 1) : d197 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d204 q = 1) : d204 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d207 q = 1) : d4340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d208 q = 1) : d4341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208, d4341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d208, d4341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56802 q = 1) : d57395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56802, d57395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56802, d57395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d56803 q = 1) : d57396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56803, d57396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56803, d57396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1620 (p : Pattern) (selected : d56815 p = 1) : d57402 p = 1 := by
  have h0 (q : Pattern) (selected : d56799 q = 1) : d56799 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56804 q = 1) : d57397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56804, d57397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1618 q selected
    | true =>
      simp only [d56804, d57397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1619 q selected
  have h2 (q : Pattern) (selected : d56806 q = 1) : d56806 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56807 q = 1) : d57398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56807, d57398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56807, d57398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56808 q = 1) : d57399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56808, d57399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56808, d57399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56809 q = 1) : d57400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56809, d57400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56809, d57400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56813 q = 1) : d56813 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56814 q = 1) : d57401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56814, d57401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56814, d57401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56815 q = 1) : d57402 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56815, d57402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56815, d57402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1621 (p : Pattern) (selected : d56831 p = 1) : d57409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d299 q = 1) : d299 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371 q = 1) : d371 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d372 q = 1) : d4372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56830 q = 1) : d57408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56830, d57408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56830, d57408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56831 q = 1) : d57409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56831, d57409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56831, d57409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1622 (p : Pattern) (selected : d56833 p = 1) : d57411 p = 1 := by
  have h0 (q : Pattern) (selected : d299 q = 1) : d299 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h3 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371 q = 1) : d371 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d372 q = 1) : d4372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56830 q = 1) : d57408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56830, d57408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56830, d57408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d379 q = 1) : d379 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d386 q = 1) : d386 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d388 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20 q selected
    | true =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h10 (q : Pattern) (selected : d389 q = 1) : d4376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d391 q = 1) : d391 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d392 q = 1) : d4377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d392, d4377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d392, d4377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56832 q = 1) : d57410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56832, d57410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56832, d57410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56833 q = 1) : d57411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56833, d57411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56833, d57411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1623 (p : Pattern) (selected : d56846 p = 1) : d57417 p = 1 := by
  have h0 (q : Pattern) (selected : d56829 q = 1) : d56829 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56834 q = 1) : d57412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56834, d57412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1621 q selected
    | true =>
      simp only [d56834, d57412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1622 q selected
  have h2 (q : Pattern) (selected : d56836 q = 1) : d56836 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56837 q = 1) : d57413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56837, d57413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56837, d57413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56838 q = 1) : d57414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56838, d57414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56838, d57414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56839 q = 1) : d57415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56839, d57415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56839, d57415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56844 q = 1) : d56844 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56845 q = 1) : d57416 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56845, d57416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56845, d57416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56846 q = 1) : d57417 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56846, d57417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56846, d57417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1624 (p : Pattern) (selected : d56852 p = 1) : d57423 p = 1 := by
  have h0 (q : Pattern) (selected : d56790 q = 1) : d56790 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d56816 q = 1) : d57403 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56816, d57403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56816, d57403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1620 q selected
  have h3 (q : Pattern) (selected : d56817 q = 1) : d57404 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56817, d57404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56817, d57404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56818 q = 1) : d57405 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56818, d57405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56818, d57405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56819 q = 1) : d57406 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56819, d57406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56819, d57406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56820 q = 1) : d57407 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56820, d57407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56820, d57407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56847 q = 1) : d57418 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56847, d57418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56847, d57418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1623 q selected
  have h8 (q : Pattern) (selected : d56848 q = 1) : d57419 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56848, d57419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56848, d57419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56849 q = 1) : d57420 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56849, d57420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56849, d57420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d56850 q = 1) : d57421 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56850, d57421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56850, d57421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d56851 q = 1) : d57422 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56851, d57422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56851, d57422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d56852 q = 1) : d57423 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56852, d57423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56852, d57423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1625 (p : Pattern) (selected : d56863 p = 1) : d57425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d517 q = 1) : d517 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d604 q = 1) : d604 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d605 q = 1) : d4409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56862 q = 1) : d57424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56862, d57424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56862, d57424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56863 q = 1) : d57425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56863, d57425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56863, d57425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1626 (p : Pattern) (selected : d56865 p = 1) : d57427 p = 1 := by
  have h0 (q : Pattern) (selected : d517 q = 1) : d517 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h3 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d604 q = 1) : d604 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d605 q = 1) : d4409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56862 q = 1) : d57424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56862, d57424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56862, d57424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d613 q = 1) : d613 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d621 q = 1) : d621 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37 q selected
    | true =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h10 (q : Pattern) (selected : d625 q = 1) : d4413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d627 q = 1) : d627 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d628 q = 1) : d4414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d628, d4414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d628, d4414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56864 q = 1) : d57426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56864, d57426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56864, d57426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56865 q = 1) : d57427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56865, d57427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56865, d57427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1627 (p : Pattern) (selected : d56881 p = 1) : d57433 p = 1 := by
  have h0 (q : Pattern) (selected : d56861 q = 1) : d56861 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56866 q = 1) : d57428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56866, d57428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1625 q selected
    | true =>
      simp only [d56866, d57428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1626 q selected
  have h2 (q : Pattern) (selected : d56871 q = 1) : d56871 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56872 q = 1) : d57429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56872, d57429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56872, d57429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56873 q = 1) : d57430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56873, d57430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56873, d57430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56874 q = 1) : d57431 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56874, d57431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56874, d57431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56879 q = 1) : d56879 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56880 q = 1) : d57432 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56880, d57432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56880, d57432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56881 q = 1) : d57433 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56881, d57433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56881, d57433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1628 (p : Pattern) (selected : d56887 p = 1) : d57439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56882 q = 1) : d57434 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56882, d57434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56882, d57434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1627 q selected
  have h2 (q : Pattern) (selected : d56883 q = 1) : d57435 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56883, d57435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56883, d57435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56884 q = 1) : d57436 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56884, d57436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56884, d57436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56885 q = 1) : d57437 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56885, d57437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56885, d57437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56886 q = 1) : d57438 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56886, d57438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56886, d57438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56887 q = 1) : d57439 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56887, d57439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56887, d57439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1629 (p : Pattern) (selected : d56899 p = 1) : d57442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d809 q = 1) : d809 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d910 q = 1) : d910 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d911 q = 1) : d4447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56898 q = 1) : d57441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56898, d57441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56898, d57441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56899 q = 1) : d57442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56899, d57442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56899, d57442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1630 (p : Pattern) (selected : d56901 p = 1) : d57444 p = 1 := by
  have h0 (q : Pattern) (selected : d809 q = 1) : d809 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h3 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d910 q = 1) : d910 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d911 q = 1) : d4447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56898 q = 1) : d57441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56898, d57441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56898, d57441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d919 q = 1) : d919 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d927 q = 1) : d927 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro61 q selected
    | true =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h10 (q : Pattern) (selected : d931 q = 1) : d4451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d933 q = 1) : d933 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d934 q = 1) : d4452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d934, d4452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d934, d4452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56900 q = 1) : d57443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56900, d57443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56900, d57443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56901 q = 1) : d57444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56901, d57444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56901, d57444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1631 (p : Pattern) (selected : d56917 p = 1) : d57450 p = 1 := by
  have h0 (q : Pattern) (selected : d56897 q = 1) : d56897 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56902 q = 1) : d57445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56902, d57445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1629 q selected
    | true =>
      simp only [d56902, d57445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1630 q selected
  have h2 (q : Pattern) (selected : d56907 q = 1) : d56907 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56908 q = 1) : d57446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56908, d57446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56908, d57446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56909 q = 1) : d57447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56909, d57447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56909, d57447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56910 q = 1) : d57448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56910, d57448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56910, d57448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56915 q = 1) : d56915 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56916 q = 1) : d57449 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56916, d57449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56916, d57449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56917 q = 1) : d57450 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56917, d57450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56917, d57450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1632 (p : Pattern) (selected : d56923 p = 1) : d57456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56918 q = 1) : d57451 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56918, d57451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56918, d57451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1631 q selected
  have h2 (q : Pattern) (selected : d56919 q = 1) : d57452 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56919, d57452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56919, d57452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56920 q = 1) : d57453 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56920, d57453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56920, d57453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56921 q = 1) : d57454 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56921, d57454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56921, d57454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56922 q = 1) : d57455 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56922, d57455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56922, d57455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56923 q = 1) : d57456 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56923, d57456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56923, d57456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1633 (p : Pattern) (selected : d56936 p = 1) : d57460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1188 q = 1) : d1188 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1321 q = 1) : d1321 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1322 q = 1) : d4486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56935 q = 1) : d57459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56935, d57459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56935, d57459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56936 q = 1) : d57460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56936, d57460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56936, d57460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1634 (p : Pattern) (selected : d56938 p = 1) : d57462 p = 1 := by
  have h0 (q : Pattern) (selected : d1188 q = 1) : d1188 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h3 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1321 q = 1) : d1321 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d1322 q = 1) : d4486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56935 q = 1) : d57459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56935, d57459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56935, d57459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1330 q = 1) : d1330 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d1338 q = 1) : d1338 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d1341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro91 q selected
    | true =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h10 (q : Pattern) (selected : d1342 q = 1) : d4490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1344 q = 1) : d1344 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1345 q = 1) : d4491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1345, d4491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1345, d4491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56937 q = 1) : d57461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56937, d57461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56937, d57461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56938 q = 1) : d57462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56938, d57462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56938, d57462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1635 (p : Pattern) (selected : d56954 p = 1) : d57468 p = 1 := by
  have h0 (q : Pattern) (selected : d56934 q = 1) : d56934 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56939 q = 1) : d57463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56939, d57463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1633 q selected
    | true =>
      simp only [d56939, d57463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1634 q selected
  have h2 (q : Pattern) (selected : d56944 q = 1) : d56944 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56945 q = 1) : d57464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56945, d57464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56945, d57464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56946 q = 1) : d57465 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56946, d57465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56946, d57465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56947 q = 1) : d57466 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56947, d57466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56947, d57466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56952 q = 1) : d56952 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56953 q = 1) : d57467 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56953, d57467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56953, d57467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56954 q = 1) : d57468 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56954, d57468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56954, d57468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1636 (p : Pattern) (selected : d56960 p = 1) : d57474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56955 q = 1) : d57469 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56955, d57469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56955, d57469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1635 q selected
  have h2 (q : Pattern) (selected : d56956 q = 1) : d57470 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56956, d57470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56956, d57470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56957 q = 1) : d57471 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56957, d57471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56957, d57471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56958 q = 1) : d57472 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56958, d57472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56958, d57472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56959 q = 1) : d57473 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56959, d57473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56959, d57473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56960 q = 1) : d57474 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56960, d57474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56960, d57474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1637 (p : Pattern) (selected : d56974 p = 1) : d57479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1649 q = 1) : d1649 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1798 q = 1) : d1798 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1799 q = 1) : d4526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56973 q = 1) : d57478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56973, d57478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56973, d57478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d56974 q = 1) : d57479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56974, d57479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56974, d57479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1638 (p : Pattern) (selected : d56976 p = 1) : d57481 p = 1 := by
  have h0 (q : Pattern) (selected : d1649 q = 1) : d1649 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h3 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1798 q = 1) : d1798 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d1799 q = 1) : d4526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56973 q = 1) : d57478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56973, d57478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56973, d57478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1807 q = 1) : d1807 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d1815 q = 1) : d1815 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d1818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro127 q selected
    | true =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h10 (q : Pattern) (selected : d1819 q = 1) : d4530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1821 q = 1) : d1821 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1822 q = 1) : d4531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1822, d4531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1822, d4531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d56975 q = 1) : d57480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d56975, d57480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d56975, d57480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d56976 q = 1) : d57481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d56976, d57481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56976, d57481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1639 (p : Pattern) (selected : d56992 p = 1) : d57487 p = 1 := by
  have h0 (q : Pattern) (selected : d56972 q = 1) : d56972 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56977 q = 1) : d57482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56977, d57482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1637 q selected
    | true =>
      simp only [d56977, d57482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1638 q selected
  have h2 (q : Pattern) (selected : d56982 q = 1) : d56982 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d56983 q = 1) : d57483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d56983, d57483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56983, d57483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d56984 q = 1) : d57484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d56984, d57484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56984, d57484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56985 q = 1) : d57485 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56985, d57485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56985, d57485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56990 q = 1) : d56990 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d56991 q = 1) : d57486 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56991, d57486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d56991, d57486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d56992 q = 1) : d57487 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56992, d57487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d56992, d57487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1640 (p : Pattern) (selected : d56998 p = 1) : d57493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d56993 q = 1) : d57488 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56993, d57488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56993, d57488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1639 q selected
  have h2 (q : Pattern) (selected : d56994 q = 1) : d57489 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56994, d57489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56994, d57489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d56995 q = 1) : d57490 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56995, d57490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56995, d57490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56996 q = 1) : d57491 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56996, d57491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56996, d57491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d56997 q = 1) : d57492 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56997, d57492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56997, d57492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56998 q = 1) : d57493 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56998, d57493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56998, d57493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1641 (p : Pattern) (selected : d57013 p = 1) : d57499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2132 q = 1) : d2132 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2276 q = 1) : d2276 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d2277 q = 1) : d4567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d57012 q = 1) : d57498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57012, d57498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57012, d57498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57013 q = 1) : d57499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57013, d57499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57013, d57499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1642 (p : Pattern) (selected : d57015 p = 1) : d57501 p = 1 := by
  have h0 (q : Pattern) (selected : d2132 q = 1) : d2132 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h3 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2276 q = 1) : d2276 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d2277 q = 1) : d4567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57012 q = 1) : d57498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57012, d57498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57012, d57498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2285 q = 1) : d2285 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d2293 q = 1) : d2293 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d2296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro164 q selected
    | true =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h10 (q : Pattern) (selected : d2297 q = 1) : d4571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2299 q = 1) : d2299 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d2300 q = 1) : d4572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2300, d4572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2300, d4572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d57014 q = 1) : d57500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57014, d57500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57014, d57500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d57015 q = 1) : d57501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57015, d57501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57015, d57501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro1643 (p : Pattern) (selected : d57031 p = 1) : d57507 p = 1 := by
  have h0 (q : Pattern) (selected : d57011 q = 1) : d57011 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57016 q = 1) : d57502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57016, d57502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1641 q selected
    | true =>
      simp only [d57016, d57502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1642 q selected
  have h2 (q : Pattern) (selected : d57021 q = 1) : d57021 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d57022 q = 1) : d57503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57022, d57503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57022, d57503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d57023 q = 1) : d57504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57023, d57504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57023, d57504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57024 q = 1) : d57505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57024, d57505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57024, d57505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d57029 q = 1) : d57029 q = 1 := by
    exact selected
  have h8 (q : Pattern) (selected : d57030 q = 1) : d57506 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57030, d57506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57030, d57506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57031 q = 1) : d57507 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57031, d57507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d57031, d57507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h9 p selected
theorem eqIntro1644 (p : Pattern) (selected : d57037 p = 1) : d57513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57032 q = 1) : d57508 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57032, d57508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57032, d57508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1643 q selected
  have h2 (q : Pattern) (selected : d57033 q = 1) : d57509 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57033, d57509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57033, d57509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57034 q = 1) : d57510 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57034, d57510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57034, d57510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57035 q = 1) : d57511 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57035, d57511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57035, d57511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57036 q = 1) : d57512 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57036, d57512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57036, d57512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57037 q = 1) : d57513 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57037, d57513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57037, d57513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1645 (p : Pattern) (selected : d57043 p = 1) : d57519 p = 1 := by
  have h0 (q : Pattern) (selected : d56888 q = 1) : d57440 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56888, d57440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1624 q selected
    | true =>
      simp only [d56888, d57440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1628 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d56924 q = 1) : d57457 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56924, d57457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56924, d57457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1632 q selected
  have h3 (q : Pattern) (selected : d56925 q = 1) : d57458 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56925, d57458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d56925, d57458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d56961 q = 1) : d57475 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56961, d57475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56961, d57475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1636 q selected
  have h5 (q : Pattern) (selected : d56962 q = 1) : d57476 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56962, d57476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56962, d57476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d56963 q = 1) : d57477 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56963, d57477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d56963, d57477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d56999 q = 1) : d57494 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56999, d57494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d56999, d57494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1640 q selected
  have h8 (q : Pattern) (selected : d57000 q = 1) : d57495 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57000, d57495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57000, d57495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57001 q = 1) : d57496 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57001, d57496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57001, d57496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57002 q = 1) : d57497 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57002, d57497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57002, d57497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57038 q = 1) : d57514 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57038, d57514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57038, d57514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1644 q selected
  have h12 (q : Pattern) (selected : d57039 q = 1) : d57515 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57039, d57515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57039, d57515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d57040 q = 1) : d57516 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57040, d57516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57040, d57516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d57041 q = 1) : d57517 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57041, d57517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57041, d57517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d57042 q = 1) : d57518 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d57042, d57518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57042, d57518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d57043 q = 1) : d57519 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d57043, d57519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d57043, d57519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1646 (p : Pattern) (selected : d57049 p = 1) : d57525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57044 q = 1) : d57520 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d57044, d57520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1645 q selected
    | true =>
      simp only [d57044, d57520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57045 q = 1) : d57521 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d57045, d57521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57045, d57521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57046 q = 1) : d57522 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d57046, d57522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57046, d57522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57047 q = 1) : d57523 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d57047, d57523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57047, d57523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57048 q = 1) : d57524 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d57048, d57524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57048, d57524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57049 q = 1) : d57525 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d57049, d57525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57049, d57525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1647 (p : Pattern) (selected : d57055 p = 1) : d57531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57050 q = 1) : d57526 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d57050, d57526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1646 q selected
    | true =>
      simp only [d57050, d57526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57051 q = 1) : d57527 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d57051, d57527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57051, d57527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57052 q = 1) : d57528 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d57052, d57528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57052, d57528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57053 q = 1) : d57529 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d57053, d57529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57053, d57529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57054 q = 1) : d57530 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d57054, d57530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57054, d57530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57055 q = 1) : d57531 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d57055, d57531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57055, d57531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1648 (p : Pattern) (selected : d57061 p = 1) : d57537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57056 q = 1) : d57532 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d57056, d57532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1647 q selected
    | true =>
      simp only [d57056, d57532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57057 q = 1) : d57533 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d57057, d57533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57057, d57533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57058 q = 1) : d57534 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d57058, d57534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57058, d57534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57059 q = 1) : d57535 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d57059, d57535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57059, d57535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57060 q = 1) : d57536 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d57060, d57536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57060, d57536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57061 q = 1) : d57537 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d57061, d57537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57061, d57537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1649 (p : Pattern) (selected : d57067 p = 1) : d57543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57062 q = 1) : d57538 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d57062, d57538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1648 q selected
    | true =>
      simp only [d57062, d57538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57063 q = 1) : d57539 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d57063, d57539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57063, d57539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57064 q = 1) : d57540 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d57064, d57540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57064, d57540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57065 q = 1) : d57541 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d57065, d57541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57065, d57541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57066 q = 1) : d57542 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d57066, d57542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57066, d57542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57067 q = 1) : d57543 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d57067, d57543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57067, d57543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1650 (p : Pattern) (selected : d57073 p = 1) : d57549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57068 q = 1) : d57544 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d57068, d57544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1649 q selected
    | true =>
      simp only [d57068, d57544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57069 q = 1) : d57545 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d57069, d57545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57069, d57545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57070 q = 1) : d57546 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d57070, d57546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57070, d57546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57071 q = 1) : d57547 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d57071, d57547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57071, d57547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57072 q = 1) : d57548 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d57072, d57548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57072, d57548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57073 q = 1) : d57549 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d57073, d57549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57073, d57549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1651 (p : Pattern) (selected : d57078 p = 1) : d57554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57074 q = 1) : d57550 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d57074, d57550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1650 q selected
    | true =>
      simp only [d57074, d57550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57075 q = 1) : d57551 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d57075, d57551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57075, d57551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57076 q = 1) : d57552 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d57076, d57552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57076, d57552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57077 q = 1) : d57553 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d57077, d57553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57077, d57553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57078 q = 1) : d57554 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d57078, d57554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57078, d57554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1652 (p : Pattern) (selected : d57084 p = 1) : d57560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d57079 q = 1) : d57555 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d57079, d57555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1651 q selected
    | true =>
      simp only [d57079, d57555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57080 q = 1) : d57556 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d57080, d57556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57080, d57556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57081 q = 1) : d57557 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d57081, d57557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57081, d57557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57082 q = 1) : d57558 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d57082, d57558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57082, d57558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57083 q = 1) : d57559 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d57083, d57559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57083, d57559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57084 q = 1) : d57560 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d57084, d57560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57084, d57560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1653 (p : Pattern) (selected : d57579 p = 0) : d57852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57577 q = 0) : d57850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57577, d57850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57577, d57850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57578 q = 0) : d57851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57578, d57851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57578, d57851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57579 q = 0) : d57852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57579, d57852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57579, d57852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1654 (p : Pattern) (selected : d57582 p = 0) : d57855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57577 q = 0) : d57850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57577, d57850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57577, d57850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57578 q = 0) : d57851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57578, d57851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57578, d57851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57580 q = 0) : d57853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57580, d57853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57580, d57853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57581 q = 0) : d57854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57581, d57854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57581, d57854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57582 q = 0) : d57855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57582, d57855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57582, d57855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1655 (p : Pattern) (selected : d57587 p = 0) : d57860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57580 q = 0) : d57853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57580, d57853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57580, d57853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57581 q = 0) : d57854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57581, d57854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57581, d57854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57587 q = 0) : d57860 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57587, d57860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57587, d57860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1656 (p : Pattern) (selected : d57595 p = 0) : d57868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57593 q = 0) : d57866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57593, d57866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57593, d57866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57594 q = 0) : d57867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57594, d57867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57594, d57867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57595 q = 0) : d57868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57595, d57868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57595, d57868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1657 (p : Pattern) (selected : d57601 p = 0) : d57874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57583 q = 0) : d57856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57583, d57856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1653 q selected
    | true =>
      simp only [d57583, d57856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1654 q selected
  have h2 (q : Pattern) (selected : d57584 q = 0) : d57857 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57584, d57857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57584, d57857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57585 q = 0) : d57858 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57585, d57858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57585, d57858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57586 q = 0) : d57859 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57586, d57859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57586, d57859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57588 q = 0) : d57861 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57588, d57861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57588, d57861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1655 q selected
  have h6 (q : Pattern) (selected : d57589 q = 0) : d57862 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57589, d57862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57589, d57862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57590 q = 0) : d57863 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57590, d57863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57590, d57863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57591 q = 0) : d57864 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57591, d57864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57591, d57864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57592 q = 0) : d57865 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57592, d57865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57592, d57865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57596 q = 0) : d57869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57596, d57869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57596, d57869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1656 q selected
  have h11 (q : Pattern) (selected : d57597 q = 0) : d57870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57597, d57870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57597, d57870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57598 q = 0) : d57871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57598, d57871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57598, d57871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57599 q = 0) : d57872 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57599, d57872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57599, d57872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57600 q = 0) : d57873 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57600, d57873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57600, d57873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57601 q = 0) : d57874 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57601, d57874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57601, d57874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1658 (p : Pattern) (selected : d57609 p = 0) : d57882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57607 q = 0) : d57880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57607, d57880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57607, d57880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57608 q = 0) : d57881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57608, d57881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57608, d57881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57609 q = 0) : d57882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57609, d57882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57609, d57882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1659 (p : Pattern) (selected : d57612 p = 0) : d57885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57607 q = 0) : d57880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57607, d57880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57607, d57880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57608 q = 0) : d57881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57608, d57881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57608, d57881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d390 q = 0) : d52156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d391 q = 0) : d52157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57610 q = 0) : d57883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57610, d57883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57610, d57883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57611 q = 0) : d57884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57611, d57884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57611, d57884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57612 q = 0) : d57885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57612, d57885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57612, d57885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1660 (p : Pattern) (selected : d57617 p = 0) : d57890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d390 q = 0) : d52156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d391 q = 0) : d52157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57610 q = 0) : d57883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57610, d57883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57610, d57883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57611 q = 0) : d57884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57611, d57884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57611, d57884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57617 q = 0) : d57890 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57617, d57890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57617, d57890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1661 (p : Pattern) (selected : d57625 p = 0) : d57898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d451 q = 0) : d52198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
    | true =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d452 q = 0) : d52199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57623 q = 0) : d57896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57623, d57896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57623, d57896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57624 q = 0) : d57897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57624, d57897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57624, d57897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57625 q = 0) : d57898 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57625, d57898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57625, d57898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1662 (p : Pattern) (selected : d57631 p = 0) : d57904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57613 q = 0) : d57886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57613, d57886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1658 q selected
    | true =>
      simp only [d57613, d57886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1659 q selected
  have h2 (q : Pattern) (selected : d57614 q = 0) : d57887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57614, d57887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57614, d57887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57615 q = 0) : d57888 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57615, d57888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57615, d57888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57616 q = 0) : d57889 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57616, d57889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57616, d57889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57618 q = 0) : d57891 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57618, d57891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57618, d57891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1660 q selected
  have h6 (q : Pattern) (selected : d57619 q = 0) : d57892 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57619, d57892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57619, d57892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57620 q = 0) : d57893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57620, d57893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57620, d57893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57621 q = 0) : d57894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57621, d57894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57621, d57894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57622 q = 0) : d57895 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57622, d57895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57622, d57895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57626 q = 0) : d57899 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57626, d57899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57626, d57899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1661 q selected
  have h11 (q : Pattern) (selected : d57627 q = 0) : d57900 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57627, d57900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57627, d57900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57628 q = 0) : d57901 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57628, d57901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57628, d57901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57629 q = 0) : d57902 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57629, d57902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57629, d57902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57630 q = 0) : d57903 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57630, d57903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57630, d57903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57631 q = 0) : d57904 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57631, d57904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57631, d57904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1663 (p : Pattern) (selected : d57637 p = 0) : d57910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57602 q = 0) : d57875 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57602, d57875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57602, d57875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1657 q selected
  have h2 (q : Pattern) (selected : d57603 q = 0) : d57876 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57603, d57876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57603, d57876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57604 q = 0) : d57877 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57604, d57877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57604, d57877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57605 q = 0) : d57878 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57605, d57878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57605, d57878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57606 q = 0) : d57879 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57606, d57879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57606, d57879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57632 q = 0) : d57905 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57632, d57905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57632, d57905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1662 q selected
  have h7 (q : Pattern) (selected : d57633 q = 0) : d57906 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57633, d57906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57633, d57906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57634 q = 0) : d57907 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57634, d57907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57634, d57907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57635 q = 0) : d57908 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57635, d57908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57635, d57908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57636 q = 0) : d57909 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57636, d57909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57636, d57909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57637 q = 0) : d57910 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57637, d57910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57637, d57910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1664 (p : Pattern) (selected : d57640 p = 0) : d57913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57638 q = 0) : d57911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57638, d57911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57638, d57911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57639 q = 0) : d57912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57639, d57912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57639, d57912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57640 q = 0) : d57913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57640, d57913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57640, d57913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1665 (p : Pattern) (selected : d57643 p = 0) : d57916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57638 q = 0) : d57911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57638, d57911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57638, d57911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57639 q = 0) : d57912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57639, d57912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57639, d57912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d626 q = 0) : d52330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d627 q = 0) : d52331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57641 q = 0) : d57914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57641, d57914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57641, d57914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57642 q = 0) : d57915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57642, d57915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57642, d57915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57643 q = 0) : d57916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57643, d57916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57643, d57916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1666 (p : Pattern) (selected : d57648 p = 0) : d57921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d626 q = 0) : d52330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d627 q = 0) : d52331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57641 q = 0) : d57914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57641, d57914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57641, d57914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57642 q = 0) : d57915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57642, d57915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57642, d57915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57648 q = 0) : d57921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57648, d57921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57648, d57921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1667 (p : Pattern) (selected : d57656 p = 0) : d57929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d720 q = 0) : d52401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro306 q selected
    | true =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d721 q = 0) : d52402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57654 q = 0) : d57927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57654, d57927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57654, d57927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57655 q = 0) : d57928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57655, d57928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57655, d57928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57656 q = 0) : d57929 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57656, d57929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57656, d57929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1668 (p : Pattern) (selected : d57662 p = 0) : d57935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57644 q = 0) : d57917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57644, d57917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1664 q selected
    | true =>
      simp only [d57644, d57917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1665 q selected
  have h2 (q : Pattern) (selected : d57645 q = 0) : d57918 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57645, d57918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57645, d57918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57646 q = 0) : d57919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57646, d57919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57646, d57919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57647 q = 0) : d57920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57647, d57920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57647, d57920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57649 q = 0) : d57922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57649, d57922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57649, d57922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1666 q selected
  have h6 (q : Pattern) (selected : d57650 q = 0) : d57923 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57650, d57923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57650, d57923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57651 q = 0) : d57924 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57651, d57924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57651, d57924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57652 q = 0) : d57925 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57652, d57925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57652, d57925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57653 q = 0) : d57926 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57653, d57926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57653, d57926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57657 q = 0) : d57930 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57657, d57930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57657, d57930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1667 q selected
  have h11 (q : Pattern) (selected : d57658 q = 0) : d57931 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57658, d57931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57658, d57931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57659 q = 0) : d57932 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57659, d57932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57659, d57932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57660 q = 0) : d57933 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57660, d57933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57660, d57933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57661 q = 0) : d57934 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57661, d57934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57661, d57934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57662 q = 0) : d57935 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57662, d57935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57662, d57935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1669 (p : Pattern) (selected : d57668 p = 0) : d57941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57663 q = 0) : d57936 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57663, d57936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57663, d57936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1668 q selected
  have h2 (q : Pattern) (selected : d57664 q = 0) : d57937 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57664, d57937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57664, d57937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57665 q = 0) : d57938 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57665, d57938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57665, d57938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57666 q = 0) : d57939 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57666, d57939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57666, d57939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57667 q = 0) : d57940 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57667, d57940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57667, d57940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57668 q = 0) : d57941 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57668, d57941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57668, d57941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1670 (p : Pattern) (selected : d57672 p = 0) : d57945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57670 q = 0) : d57943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57670, d57943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57670, d57943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57671 q = 0) : d57944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57671, d57944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57671, d57944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57672 q = 0) : d57945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57672, d57945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57672, d57945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1671 (p : Pattern) (selected : d57675 p = 0) : d57948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57670 q = 0) : d57943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57670, d57943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57670, d57943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57671 q = 0) : d57944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57671, d57944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57671, d57944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d932 q = 0) : d52551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d933 q = 0) : d52552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57673 q = 0) : d57946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57673, d57946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57673, d57946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57674 q = 0) : d57947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57674, d57947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57674, d57947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57675 q = 0) : d57948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57675, d57948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57675, d57948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1672 (p : Pattern) (selected : d57680 p = 0) : d57953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d932 q = 0) : d52551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d933 q = 0) : d52552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57673 q = 0) : d57946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57673, d57946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57673, d57946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57674 q = 0) : d57947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57674, d57947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57674, d57947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57680 q = 0) : d57953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57680, d57953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57680, d57953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1673 (p : Pattern) (selected : d57688 p = 0) : d57961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1053 q = 0) : d52638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro371 q selected
    | true =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1054 q = 0) : d52639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57686 q = 0) : d57959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57686, d57959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57686, d57959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57687 q = 0) : d57960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57687, d57960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57687, d57960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57688 q = 0) : d57961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57688, d57961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57688, d57961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1674 (p : Pattern) (selected : d57694 p = 0) : d57967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57676 q = 0) : d57949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57676, d57949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1670 q selected
    | true =>
      simp only [d57676, d57949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1671 q selected
  have h2 (q : Pattern) (selected : d57677 q = 0) : d57950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57677, d57950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57677, d57950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57678 q = 0) : d57951 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57678, d57951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57678, d57951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57679 q = 0) : d57952 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57679, d57952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57679, d57952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57681 q = 0) : d57954 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57681, d57954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57681, d57954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1672 q selected
  have h6 (q : Pattern) (selected : d57682 q = 0) : d57955 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57682, d57955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57682, d57955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57683 q = 0) : d57956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57683, d57956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57683, d57956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57684 q = 0) : d57957 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57684, d57957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57684, d57957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57685 q = 0) : d57958 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57685, d57958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57685, d57958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57689 q = 0) : d57962 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57689, d57962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57689, d57962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1673 q selected
  have h11 (q : Pattern) (selected : d57690 q = 0) : d57963 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57690, d57963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57690, d57963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57691 q = 0) : d57964 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57691, d57964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57691, d57964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57692 q = 0) : d57965 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57692, d57965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57692, d57965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57693 q = 0) : d57966 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57693, d57966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57693, d57966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57694 q = 0) : d57967 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57694, d57967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57694, d57967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1675 (p : Pattern) (selected : d57700 p = 0) : d57973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57695 q = 0) : d57968 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57695, d57968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57695, d57968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1674 q selected
  have h2 (q : Pattern) (selected : d57696 q = 0) : d57969 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57696, d57969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57696, d57969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57697 q = 0) : d57970 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57697, d57970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57697, d57970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57698 q = 0) : d57971 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57698, d57971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57698, d57971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57699 q = 0) : d57972 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57699, d57972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57699, d57972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57700 q = 0) : d57973 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57700, d57973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57700, d57973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1676 (p : Pattern) (selected : d57705 p = 0) : d57978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57703 q = 0) : d57976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57703, d57976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57703, d57976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57704 q = 0) : d57977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57704, d57977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57704, d57977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57705 q = 0) : d57978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57705, d57978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57705, d57978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1677 (p : Pattern) (selected : d57708 p = 0) : d57981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57703 q = 0) : d57976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57703, d57976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57703, d57976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57704 q = 0) : d57977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57704, d57977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57704, d57977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1343 q = 0) : d52831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1344 q = 0) : d52832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57706 q = 0) : d57979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57706, d57979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57706, d57979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57707 q = 0) : d57980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57707, d57980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57707, d57980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57708 q = 0) : d57981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57708, d57981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57708, d57981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1678 (p : Pattern) (selected : d57713 p = 0) : d57986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1343 q = 0) : d52831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1344 q = 0) : d52832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57706 q = 0) : d57979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57706, d57979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57706, d57979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57707 q = 0) : d57980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57707, d57980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57707, d57980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57713 q = 0) : d57986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57713, d57986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57713, d57986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1679 (p : Pattern) (selected : d57721 p = 0) : d57994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1487 q = 0) : d52932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro447 q selected
    | true =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1488 q = 0) : d52933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57719 q = 0) : d57992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57719, d57992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57719, d57992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57720 q = 0) : d57993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57720, d57993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57720, d57993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57721 q = 0) : d57994 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57721, d57994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57721, d57994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1680 (p : Pattern) (selected : d57727 p = 0) : d58000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57709 q = 0) : d57982 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57709, d57982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1676 q selected
    | true =>
      simp only [d57709, d57982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1677 q selected
  have h2 (q : Pattern) (selected : d57710 q = 0) : d57983 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57710, d57983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57710, d57983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57711 q = 0) : d57984 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57711, d57984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57711, d57984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57712 q = 0) : d57985 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57712, d57985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57712, d57985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57714 q = 0) : d57987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57714, d57987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57714, d57987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1678 q selected
  have h6 (q : Pattern) (selected : d57715 q = 0) : d57988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57715, d57988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57715, d57988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57716 q = 0) : d57989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57716, d57989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57716, d57989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57717 q = 0) : d57990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57717, d57990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57717, d57990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57718 q = 0) : d57991 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57718, d57991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57718, d57991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57722 q = 0) : d57995 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57722, d57995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57722, d57995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1679 q selected
  have h11 (q : Pattern) (selected : d57723 q = 0) : d57996 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57723, d57996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57723, d57996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57724 q = 0) : d57997 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57724, d57997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57724, d57997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57725 q = 0) : d57998 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57725, d57998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57725, d57998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57726 q = 0) : d57999 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57726, d57999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57726, d57999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57727 q = 0) : d58000 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57727, d58000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57727, d58000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1681 (p : Pattern) (selected : d57733 p = 0) : d58006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57728 q = 0) : d58001 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57728, d58001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57728, d58001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1680 q selected
  have h2 (q : Pattern) (selected : d57729 q = 0) : d58002 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57729, d58002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57729, d58002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57730 q = 0) : d58003 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57730, d58003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57730, d58003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57731 q = 0) : d58004 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57731, d58004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57731, d58004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57732 q = 0) : d58005 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57732, d58005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57732, d58005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57733 q = 0) : d58006 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57733, d58006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57733, d58006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1682 (p : Pattern) (selected : d57739 p = 0) : d58012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57737 q = 0) : d58010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57737, d58010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57737, d58010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57738 q = 0) : d58011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57738, d58011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57738, d58011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57739 q = 0) : d58012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57739, d58012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57739, d58012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1683 (p : Pattern) (selected : d57742 p = 0) : d58015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57737 q = 0) : d58010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57737, d58010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57737, d58010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57738 q = 0) : d58011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57738, d58011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57738, d58011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1820 q = 0) : d53146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1821 q = 0) : d53147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57740 q = 0) : d58013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57740, d58013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57740, d58013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57741 q = 0) : d58014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57741, d58014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57741, d58014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57742 q = 0) : d58015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57742, d58015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57742, d58015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1684 (p : Pattern) (selected : d57747 p = 0) : d58020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1820 q = 0) : d53146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1821 q = 0) : d53147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57740 q = 0) : d58013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57740, d58013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57740, d58013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57741 q = 0) : d58014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57741, d58014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57741, d58014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57747 q = 0) : d58020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57747, d58020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57747, d58020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1685 (p : Pattern) (selected : d57755 p = 0) : d58028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1964 q = 0) : d53247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro533 q selected
    | true =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1965 q = 0) : d53248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57753 q = 0) : d58026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57753, d58026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57753, d58026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57754 q = 0) : d58027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57754, d58027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57754, d58027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57755 q = 0) : d58028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57755, d58028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57755, d58028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1686 (p : Pattern) (selected : d57761 p = 0) : d58034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57743 q = 0) : d58016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57743, d58016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1682 q selected
    | true =>
      simp only [d57743, d58016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1683 q selected
  have h2 (q : Pattern) (selected : d57744 q = 0) : d58017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57744, d58017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57744, d58017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57745 q = 0) : d58018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57745, d58018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57745, d58018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57746 q = 0) : d58019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57746, d58019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57746, d58019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57748 q = 0) : d58021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57748, d58021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57748, d58021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1684 q selected
  have h6 (q : Pattern) (selected : d57749 q = 0) : d58022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57749, d58022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57749, d58022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57750 q = 0) : d58023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57750, d58023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57750, d58023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57751 q = 0) : d58024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57751, d58024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57751, d58024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57752 q = 0) : d58025 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57752, d58025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57752, d58025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57756 q = 0) : d58029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57756, d58029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57756, d58029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1685 q selected
  have h11 (q : Pattern) (selected : d57757 q = 0) : d58030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57757, d58030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57757, d58030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57758 q = 0) : d58031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57758, d58031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57758, d58031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57759 q = 0) : d58032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57759, d58032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57759, d58032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57760 q = 0) : d58033 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57760, d58033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57760, d58033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57761 q = 0) : d58034 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57761, d58034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57761, d58034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1687 (p : Pattern) (selected : d57767 p = 0) : d58040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57762 q = 0) : d58035 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57762, d58035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57762, d58035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1686 q selected
  have h2 (q : Pattern) (selected : d57763 q = 0) : d58036 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57763, d58036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57763, d58036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57764 q = 0) : d58037 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57764, d58037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57764, d58037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57765 q = 0) : d58038 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57765, d58038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57765, d58038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57766 q = 0) : d58039 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57766, d58039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57766, d58039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57767 q = 0) : d58040 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57767, d58040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57767, d58040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1688 (p : Pattern) (selected : d57774 p = 0) : d58047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57772 q = 0) : d58045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57772, d58045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57772, d58045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57773 q = 0) : d58046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57773, d58046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57773, d58046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57774 q = 0) : d58047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57774, d58047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57774, d58047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1689 (p : Pattern) (selected : d57777 p = 0) : d58050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57772 q = 0) : d58045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57772, d58045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57772, d58045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57773 q = 0) : d58046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57773, d58046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57773, d58046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2298 q = 0) : d53463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2299 q = 0) : d53464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57775 q = 0) : d58048 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57775, d58048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57775, d58048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d57776 q = 0) : d58049 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57776, d58049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57776, d58049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57777 q = 0) : d58050 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57777, d58050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57777, d58050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1690 (p : Pattern) (selected : d57782 p = 0) : d58055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2298 q = 0) : d53463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2299 q = 0) : d53464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57775 q = 0) : d58048 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57775, d58048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57775, d58048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57776 q = 0) : d58049 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57776, d58049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57776, d58049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57782 q = 0) : d58055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57782, d58055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57782, d58055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1691 (p : Pattern) (selected : d57790 p = 0) : d58063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2442 q = 0) : d53564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro623 q selected
    | true =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2443 q = 0) : d53565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57788 q = 0) : d58061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d57788, d58061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57788, d58061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57789 q = 0) : d58062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d57789, d58062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57789, d58062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57790 q = 0) : d58063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d57790, d58063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57790, d58063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1692 (p : Pattern) (selected : d57796 p = 0) : d58069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57778 q = 0) : d58051 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57778, d58051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1688 q selected
    | true =>
      simp only [d57778, d58051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1689 q selected
  have h2 (q : Pattern) (selected : d57779 q = 0) : d58052 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57779, d58052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57779, d58052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57780 q = 0) : d58053 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57780, d58053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57780, d58053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57781 q = 0) : d58054 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57781, d58054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57781, d58054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57783 q = 0) : d58056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57783, d58056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57783, d58056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1690 q selected
  have h6 (q : Pattern) (selected : d57784 q = 0) : d58057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57784, d58057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57784, d58057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d57785 q = 0) : d58058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57785, d58058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57785, d58058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d57786 q = 0) : d58059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57786, d58059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d57786, d58059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d57787 q = 0) : d58060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57787, d58060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57787, d58060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57791 q = 0) : d58064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d57791, d58064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57791, d58064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1691 q selected
  have h11 (q : Pattern) (selected : d57792 q = 0) : d58065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57792, d58065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57792, d58065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d57793 q = 0) : d58066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d57793, d58066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d57793, d58066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d57794 q = 0) : d58067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d57794, d58067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d57794, d58067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d57795 q = 0) : d58068 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d57795, d58068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d57795, d58068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d57796 q = 0) : d58069 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d57796, d58069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d57796, d58069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1693 (p : Pattern) (selected : d57802 p = 0) : d58075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57797 q = 0) : d58070 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d57797, d58070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57797, d58070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1692 q selected
  have h2 (q : Pattern) (selected : d57798 q = 0) : d58071 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d57798, d58071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57798, d58071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d57799 q = 0) : d58072 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d57799, d58072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57799, d58072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57800 q = 0) : d58073 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d57800, d58073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57800, d58073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d57801 q = 0) : d58074 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d57801, d58074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57801, d58074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57802 q = 0) : d58075 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d57802, d58075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57802, d58075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1694 (p : Pattern) (selected : d57808 p = 0) : d58081 p = 1 := by
  have h0 (q : Pattern) (selected : d57669 q = 0) : d57942 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57669, d57942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1663 q selected
    | true =>
      simp only [d57669, d57942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1669 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d57701 q = 0) : d57974 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57701, d57974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57701, d57974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1675 q selected
  have h3 (q : Pattern) (selected : d57702 q = 0) : d57975 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57702, d57975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57702, d57975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d57734 q = 0) : d58007 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57734, d58007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57734, d58007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1681 q selected
  have h5 (q : Pattern) (selected : d57735 q = 0) : d58008 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57735, d58008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57735, d58008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d57736 q = 0) : d58009 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57736, d58009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57736, d58009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d57768 q = 0) : d58041 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57768, d58041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57768, d58041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1687 q selected
  have h8 (q : Pattern) (selected : d57769 q = 0) : d58042 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57769, d58042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57769, d58042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d57770 q = 0) : d58043 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57770, d58043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57770, d58043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d57771 q = 0) : d58044 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57771, d58044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d57771, d58044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d57803 q = 0) : d58076 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d57803, d58076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57803, d58076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1693 q selected
  have h12 (q : Pattern) (selected : d57804 q = 0) : d58077 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d57804, d58077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57804, d58077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d57805 q = 0) : d58078 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d57805, d58078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57805, d58078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d57806 q = 0) : d58079 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d57806, d58079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57806, d58079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d57807 q = 0) : d58080 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d57807, d58080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d57807, d58080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d57808 q = 0) : d58081 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d57808, d58081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d57808, d58081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1695 (p : Pattern) (selected : d57814 p = 0) : d58087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57809 q = 0) : d58082 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d57809, d58082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1694 q selected
    | true =>
      simp only [d57809, d58082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57810 q = 0) : d58083 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d57810, d58083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57810, d58083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57811 q = 0) : d58084 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d57811, d58084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57811, d58084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57812 q = 0) : d58085 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d57812, d58085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57812, d58085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57813 q = 0) : d58086 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d57813, d58086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57813, d58086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57814 q = 0) : d58087 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d57814, d58087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57814, d58087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1696 (p : Pattern) (selected : d57820 p = 0) : d58093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57815 q = 0) : d58088 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d57815, d58088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1695 q selected
    | true =>
      simp only [d57815, d58088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57816 q = 0) : d58089 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d57816, d58089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57816, d58089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57817 q = 0) : d58090 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d57817, d58090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57817, d58090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57818 q = 0) : d58091 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d57818, d58091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57818, d58091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57819 q = 0) : d58092 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d57819, d58092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57819, d58092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57820 q = 0) : d58093 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d57820, d58093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57820, d58093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1697 (p : Pattern) (selected : d57826 p = 0) : d58099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57821 q = 0) : d58094 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d57821, d58094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1696 q selected
    | true =>
      simp only [d57821, d58094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57822 q = 0) : d58095 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d57822, d58095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57822, d58095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57823 q = 0) : d58096 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d57823, d58096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57823, d58096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57824 q = 0) : d58097 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d57824, d58097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57824, d58097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57825 q = 0) : d58098 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d57825, d58098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57825, d58098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57826 q = 0) : d58099 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d57826, d58099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57826, d58099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1698 (p : Pattern) (selected : d57832 p = 0) : d58105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57827 q = 0) : d58100 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d57827, d58100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1697 q selected
    | true =>
      simp only [d57827, d58100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57828 q = 0) : d58101 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d57828, d58101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57828, d58101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57829 q = 0) : d58102 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d57829, d58102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57829, d58102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57830 q = 0) : d58103 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d57830, d58103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57830, d58103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57831 q = 0) : d58104 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d57831, d58104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57831, d58104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57832 q = 0) : d58105 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d57832, d58105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57832, d58105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1699 (p : Pattern) (selected : d57838 p = 0) : d58111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57833 q = 0) : d58106 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d57833, d58106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1698 q selected
    | true =>
      simp only [d57833, d58106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57834 q = 0) : d58107 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d57834, d58107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57834, d58107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57835 q = 0) : d58108 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d57835, d58108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57835, d58108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57836 q = 0) : d58109 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d57836, d58109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57836, d58109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57837 q = 0) : d58110 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d57837, d58110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57837, d58110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57838 q = 0) : d58111 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d57838, d58111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57838, d58111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1700 (p : Pattern) (selected : d57843 p = 0) : d58116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57839 q = 0) : d58112 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d57839, d58112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1699 q selected
    | true =>
      simp only [d57839, d58112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57840 q = 0) : d58113 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d57840, d58113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57840, d58113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57841 q = 0) : d58114 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d57841, d58114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57841, d58114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57842 q = 0) : d58115 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d57842, d58115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57842, d58115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57843 q = 0) : d58116 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d57843, d58116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57843, d58116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1701 (p : Pattern) (selected : d57849 p = 0) : d58122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d57844 q = 0) : d58117 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d57844, d58117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1700 q selected
    | true =>
      simp only [d57844, d58117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d57845 q = 0) : d58118 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d57845, d58118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57845, d58118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d57846 q = 0) : d58119 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d57846, d58119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d57846, d58119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d57847 q = 0) : d58120 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d57847, d58120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d57847, d58120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d57848 q = 0) : d58121 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d57848, d58121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d57848, d58121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d57849 q = 0) : d58122 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d57849, d58122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d57849, d58122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1702 (p : Pattern) (selected : d57849 p = 1) : d57849 p = 1 := by
  have h0 (q : Pattern) (selected : d57849 q = 1) : d57849 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro1703 (p : Pattern) (selected : d94 p = 0) : d51946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90 q = 0) : d51942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d51942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90, d51942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro198 q selected
  have h2 (q : Pattern) (selected : d91 q = 0) : d51943 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d51943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d91, d51943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d92 q = 0) : d51944 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, d51944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d92, d51944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d93 q = 0) : d51945 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, d51945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d93, d51945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94 q = 0) : d51946 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, d51946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94, d51946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1704 (p : Pattern) (selected : d273 p = 0) : d52072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d269 q = 0) : d52068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269, d52068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d269, d52068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro228 q selected
  have h2 (q : Pattern) (selected : d270 q = 0) : d52069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270, d52069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d270, d52069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d271 q = 0) : d52070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271, d52070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271, d52070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d272 q = 0) : d52071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d272, d52071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d272, d52071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d273 q = 0) : d52072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273, d52072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d273, d52072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1705 (p : Pattern) (selected : d467 p = 0) : d52214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d457 q = 0) : d52204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d457, d52204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d457, d52204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro259 q selected
  have h2 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h3 (q : Pattern) (selected : d464 q = 0) : d52211 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d464, d52211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d464, d52211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d465 q = 0) : d52212 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d465, d52212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d465, d52212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d466 q = 0) : d52213 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d466, d52213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d466, d52213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d467 q = 0) : d52214 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d467, d52214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d467, d52214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1706 (p : Pattern) (selected : d58144 p = 0) : d58246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58130 q = 0) : d58232 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58130, d58232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58130, d58232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1703 q selected
  have h2 (q : Pattern) (selected : d58131 q = 0) : d58233 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58131, d58233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58131, d58233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58132 q = 0) : d58234 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58132, d58234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58132, d58234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58133 q = 0) : d58235 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58133, d58235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58133, d58235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58134 q = 0) : d58236 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58134, d58236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58134, d58236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1704 q selected
  have h6 (q : Pattern) (selected : d58135 q = 0) : d58237 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58135, d58237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58135, d58237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58136 q = 0) : d58238 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58136, d58238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58136, d58238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58137 q = 0) : d58239 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58137, d58239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58137, d58239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58138 q = 0) : d58240 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58138, d58240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58138, d58240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58139 q = 0) : d58241 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58139, d58241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58139, d58241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1705 q selected
  have h11 (q : Pattern) (selected : d58140 q = 0) : d58242 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58140, d58242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58140, d58242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d58141 q = 0) : d58243 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58141, d58243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58141, d58243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58142 q = 0) : d58244 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58142, d58244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58142, d58244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58143 q = 0) : d58245 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58143, d58245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58143, d58245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58144 q = 0) : d58246 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58144, d58246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58144, d58246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1707 (p : Pattern) (selected : d741 p = 0) : d52418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d726 q = 0) : d52407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d726, d52407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d726, d52407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro312 q selected
  have h2 (q : Pattern) (selected : d737 q = 0) : d52414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro314 q selected
  have h3 (q : Pattern) (selected : d738 q = 0) : d52415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d738, d52415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d738, d52415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d739 q = 0) : d52416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d739, d52416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d739, d52416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d740 q = 0) : d52417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d740, d52417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d740, d52417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d741 q = 0) : d52418 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d741, d52418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d741, d52418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1708 (p : Pattern) (selected : d58150 p = 0) : d58252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58145 q = 0) : d58247 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58145, d58247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58145, d58247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1707 q selected
  have h2 (q : Pattern) (selected : d58146 q = 0) : d58248 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58146, d58248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58146, d58248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58147 q = 0) : d58249 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58147, d58249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58147, d58249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58148 q = 0) : d58250 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58148, d58250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58148, d58250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58149 q = 0) : d58251 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58149, d58251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58149, d58251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58150 q = 0) : d58252 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58150, d58252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58150, d58252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1709 (p : Pattern) (selected : d1074 p = 0) : d52655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1059 q = 0) : d52644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1059, d52644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1059, d52644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro379 q selected
  have h2 (q : Pattern) (selected : d1070 q = 0) : d52651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro381 q selected
  have h3 (q : Pattern) (selected : d1071 q = 0) : d52652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1071, d52652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1071, d52652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1072 q = 0) : d52653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1072, d52653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1072, d52653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1073 q = 0) : d52654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1073, d52654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1073, d52654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1074 q = 0) : d52655 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1074, d52655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1074, d52655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1710 (p : Pattern) (selected : d58157 p = 0) : d58259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58152 q = 0) : d58254 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58152, d58254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58152, d58254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1709 q selected
  have h2 (q : Pattern) (selected : d58153 q = 0) : d58255 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58153, d58255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58153, d58255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58154 q = 0) : d58256 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58154, d58256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58154, d58256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58155 q = 0) : d58257 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58155, d58257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58155, d58257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58156 q = 0) : d58258 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58156, d58258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58156, d58258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58157 q = 0) : d58259 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58157, d58259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58157, d58259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1711 (p : Pattern) (selected : d1508 p = 0) : d52949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1493 q = 0) : d52938 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1493, d52938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1493, d52938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro455 q selected
  have h2 (q : Pattern) (selected : d1504 q = 0) : d52945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro457 q selected
  have h3 (q : Pattern) (selected : d1505 q = 0) : d52946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1505, d52946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1505, d52946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1506 q = 0) : d52947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1506, d52947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1506, d52947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1507 q = 0) : d52948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1507, d52948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1507, d52948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1508 q = 0) : d52949 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1508, d52949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1508, d52949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1712 (p : Pattern) (selected : d58165 p = 0) : d58267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58160 q = 0) : d58262 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58160, d58262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58160, d58262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1711 q selected
  have h2 (q : Pattern) (selected : d58161 q = 0) : d58263 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58161, d58263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58161, d58263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58162 q = 0) : d58264 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58162, d58264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58162, d58264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58163 q = 0) : d58265 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58163, d58265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58163, d58265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58164 q = 0) : d58266 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58164, d58266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58164, d58266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58165 q = 0) : d58267 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58165, d58267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58165, d58267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1713 (p : Pattern) (selected : d1985 p = 0) : d53264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1970 q = 0) : d53253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1970, d53253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1970, d53253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro541 q selected
  have h2 (q : Pattern) (selected : d1981 q = 0) : d53260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro543 q selected
  have h3 (q : Pattern) (selected : d1982 q = 0) : d53261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1982, d53261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1982, d53261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1983 q = 0) : d53262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1983, d53262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1983, d53262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1984 q = 0) : d53263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1984, d53263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1984, d53263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1985 q = 0) : d53264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1985, d53264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1985, d53264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1714 (p : Pattern) (selected : d58174 p = 0) : d58276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58169 q = 0) : d58271 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58169, d58271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58169, d58271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1713 q selected
  have h2 (q : Pattern) (selected : d58170 q = 0) : d58272 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58170, d58272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58170, d58272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58171 q = 0) : d58273 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58171, d58273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58171, d58273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58172 q = 0) : d58274 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58172, d58274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58172, d58274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58173 q = 0) : d58275 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58173, d58275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58173, d58275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58174 q = 0) : d58276 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58174, d58276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58174, d58276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1715 (p : Pattern) (selected : d2463 p = 0) : d53581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2448 q = 0) : d53570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2448, d53570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2448, d53570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro631 q selected
  have h2 (q : Pattern) (selected : d2459 q = 0) : d53577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro633 q selected
  have h3 (q : Pattern) (selected : d2460 q = 0) : d53578 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2460, d53578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2460, d53578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2461 q = 0) : d53579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2461, d53579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2461, d53579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2462 q = 0) : d53580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2462, d53580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2462, d53580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2463 q = 0) : d53581 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2463, d53581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2463, d53581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1716 (p : Pattern) (selected : d58184 p = 0) : d58286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58179 q = 0) : d58281 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58179, d58281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58179, d58281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1715 q selected
  have h2 (q : Pattern) (selected : d58180 q = 0) : d58282 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58180, d58282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58180, d58282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58181 q = 0) : d58283 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58181, d58283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58181, d58283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58182 q = 0) : d58284 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58182, d58284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58182, d58284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58183 q = 0) : d58285 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58183, d58285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58183, d58285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58184 q = 0) : d58286 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58184, d58286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58184, d58286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1717 (p : Pattern) (selected : d58190 p = 0) : d58292 p = 1 := by
  have h0 (q : Pattern) (selected : d58151 q = 0) : d58253 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58151, d58253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1706 q selected
    | true =>
      simp only [d58151, d58253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1708 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d58158 q = 0) : d58260 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58158, d58260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58158, d58260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1710 q selected
  have h3 (q : Pattern) (selected : d58159 q = 0) : d58261 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58159, d58261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58159, d58261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58166 q = 0) : d58268 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58166, d58268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58166, d58268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1712 q selected
  have h5 (q : Pattern) (selected : d58167 q = 0) : d58269 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58167, d58269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58167, d58269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58168 q = 0) : d58270 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58168, d58270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58168, d58270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58175 q = 0) : d58277 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58175, d58277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58175, d58277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1714 q selected
  have h8 (q : Pattern) (selected : d58176 q = 0) : d58278 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58176, d58278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58176, d58278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58177 q = 0) : d58279 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58177, d58279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58177, d58279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58178 q = 0) : d58280 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58178, d58280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58178, d58280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58185 q = 0) : d58287 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58185, d58287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58185, d58287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1716 q selected
  have h12 (q : Pattern) (selected : d58186 q = 0) : d58288 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58186, d58288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58186, d58288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58187 q = 0) : d58289 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58187, d58289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58187, d58289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58188 q = 0) : d58290 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58188, d58290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58188, d58290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58189 q = 0) : d58291 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58189, d58291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58189, d58291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d58190 q = 0) : d58292 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58190, d58292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58190, d58292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1718 (p : Pattern) (selected : d58196 p = 0) : d58298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58191 q = 0) : d58293 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58191, d58293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1717 q selected
    | true =>
      simp only [d58191, d58293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58192 q = 0) : d58294 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58192, d58294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58192, d58294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58193 q = 0) : d58295 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58193, d58295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58193, d58295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58194 q = 0) : d58296 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58194, d58296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58194, d58296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58195 q = 0) : d58297 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58195, d58297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58195, d58297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58196 q = 0) : d58298 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58196, d58298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58196, d58298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1719 (p : Pattern) (selected : d58202 p = 0) : d58304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58197 q = 0) : d58299 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58197, d58299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1718 q selected
    | true =>
      simp only [d58197, d58299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58198 q = 0) : d58300 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58198, d58300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58198, d58300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58199 q = 0) : d58301 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58199, d58301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58199, d58301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58200 q = 0) : d58302 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58200, d58302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58200, d58302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58201 q = 0) : d58303 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58201, d58303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58201, d58303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58202 q = 0) : d58304 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58202, d58304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58202, d58304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1720 (p : Pattern) (selected : d58208 p = 0) : d58310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58203 q = 0) : d58305 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58203, d58305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1719 q selected
    | true =>
      simp only [d58203, d58305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58204 q = 0) : d58306 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58204, d58306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58204, d58306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58205 q = 0) : d58307 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58205, d58307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58205, d58307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58206 q = 0) : d58308 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58206, d58308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58206, d58308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58207 q = 0) : d58309 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58207, d58309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58207, d58309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58208 q = 0) : d58310 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58208, d58310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58208, d58310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1721 (p : Pattern) (selected : d58214 p = 0) : d58316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58209 q = 0) : d58311 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58209, d58311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1720 q selected
    | true =>
      simp only [d58209, d58311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58210 q = 0) : d58312 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58210, d58312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58210, d58312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58211 q = 0) : d58313 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58211, d58313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58211, d58313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58212 q = 0) : d58314 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58212, d58314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58212, d58314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58213 q = 0) : d58315 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58213, d58315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58213, d58315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58214 q = 0) : d58316 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58214, d58316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58214, d58316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1722 (p : Pattern) (selected : d58220 p = 0) : d58322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58215 q = 0) : d58317 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58215, d58317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1721 q selected
    | true =>
      simp only [d58215, d58317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58216 q = 0) : d58318 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58216, d58318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58216, d58318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58217 q = 0) : d58319 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58217, d58319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58217, d58319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58218 q = 0) : d58320 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58218, d58320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58218, d58320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58219 q = 0) : d58321 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58219, d58321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58219, d58321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58220 q = 0) : d58322 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58220, d58322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58220, d58322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1723 (p : Pattern) (selected : d58225 p = 0) : d58327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58221 q = 0) : d58323 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58221, d58323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1722 q selected
    | true =>
      simp only [d58221, d58323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58222 q = 0) : d58324 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58222, d58324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58222, d58324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58223 q = 0) : d58325 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58223, d58325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58223, d58325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58224 q = 0) : d58326 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58224, d58326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58224, d58326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58225 q = 0) : d58327 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58225, d58327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58225, d58327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1724 (p : Pattern) (selected : d58231 p = 0) : d58333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58226 q = 0) : d58328 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58226, d58328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1723 q selected
    | true =>
      simp only [d58226, d58328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58227 q = 0) : d58329 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58227, d58329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58227, d58329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58228 q = 0) : d58330 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58228, d58330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58228, d58330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58229 q = 0) : d58331 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58229, d58331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58229, d58331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58230 q = 0) : d58332 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58230, d58332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58230, d58332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58231 q = 0) : d58333 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58231, d58333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58231, d58333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1725 (p : Pattern) (selected : d273 p = 1) : d4364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d269 q = 1) : d4360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269, d4360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d269, d4360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12 q selected
  have h2 (q : Pattern) (selected : d270 q = 1) : d4361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270, d4361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d270, d4361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d271 q = 1) : d4362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271, d4362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271, d4362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d272 q = 1) : d4363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d272, d4363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d272, d4363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d273 q = 1) : d4364 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273, d4364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d273, d4364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1726 (p : Pattern) (selected : d467 p = 1) : d51675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d457 q = 1) : d4396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d457, d4396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d457, d4396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26 q selected
  have h2 (q : Pattern) (selected : d463 q = 1) : d463 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d464 q = 1) : d51672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d464, d51672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d464, d51672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d465 q = 1) : d51673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d465, d51673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d465, d51673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d466 q = 1) : d51674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d466, d51674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d466, d51674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d467 q = 1) : d51675 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d467, d51675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d467, d51675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1727 (p : Pattern) (selected : d58144 p = 1) : d58344 p = 1 := by
  have h0 (q : Pattern) (selected : d58133 q = 1) : d58133 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58134 q = 1) : d58334 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58134, d58334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58134, d58334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1725 q selected
  have h3 (q : Pattern) (selected : d58135 q = 1) : d58335 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58135, d58335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58135, d58335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58136 q = 1) : d58336 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58136, d58336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58136, d58336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58137 q = 1) : d58337 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58137, d58337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58137, d58337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58138 q = 1) : d58338 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58138, d58338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58138, d58338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58139 q = 1) : d58339 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58139, d58339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58139, d58339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1726 q selected
  have h8 (q : Pattern) (selected : d58140 q = 1) : d58340 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58140, d58340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58140, d58340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58141 q = 1) : d58341 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58141, d58341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58141, d58341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58142 q = 1) : d58342 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58142, d58342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58142, d58342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58143 q = 1) : d58343 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58143, d58343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58143, d58343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d58144 q = 1) : d58344 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58144, d58344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58144, d58344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1728 (p : Pattern) (selected : d741 p = 1) : d51700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d726 q = 1) : d4433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d726, d4433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d726, d4433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro46 q selected
  have h2 (q : Pattern) (selected : d737 q = 1) : d737 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d738 q = 1) : d51697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d738, d51697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d738, d51697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d739 q = 1) : d51698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d739, d51698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d739, d51698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d740 q = 1) : d51699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d740, d51699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d740, d51699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d741 q = 1) : d51700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d741, d51700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d741, d51700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1729 (p : Pattern) (selected : d58150 p = 1) : d58350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58145 q = 1) : d58345 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58145, d58345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58145, d58345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1728 q selected
  have h2 (q : Pattern) (selected : d58146 q = 1) : d58346 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58146, d58346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58146, d58346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58147 q = 1) : d58347 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58147, d58347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58147, d58347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58148 q = 1) : d58348 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58148, d58348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58148, d58348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58149 q = 1) : d58349 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58149, d58349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58149, d58349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58150 q = 1) : d58350 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58150, d58350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58150, d58350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1730 (p : Pattern) (selected : d1074 p = 1) : d51726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1059 q = 1) : d4471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1059, d4471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1059, d4471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro72 q selected
  have h2 (q : Pattern) (selected : d1070 q = 1) : d1070 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1071 q = 1) : d51723 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1071, d51723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1071, d51723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1072 q = 1) : d51724 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1072, d51724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1072, d51724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1073 q = 1) : d51725 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1073, d51725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1073, d51725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1074 q = 1) : d51726 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1074, d51726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1074, d51726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1731 (p : Pattern) (selected : d58157 p = 1) : d58357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58152 q = 1) : d58352 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58152, d58352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58152, d58352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1730 q selected
  have h2 (q : Pattern) (selected : d58153 q = 1) : d58353 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58153, d58353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58153, d58353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58154 q = 1) : d58354 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58154, d58354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58154, d58354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58155 q = 1) : d58355 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58155, d58355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58155, d58355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58156 q = 1) : d58356 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58156, d58356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58156, d58356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58157 q = 1) : d58357 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58157, d58357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58157, d58357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1732 (p : Pattern) (selected : d1508 p = 1) : d51753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1493 q = 1) : d4510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1493, d4510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1493, d4510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro102 q selected
  have h2 (q : Pattern) (selected : d1504 q = 1) : d1504 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1505 q = 1) : d51750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1505, d51750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1505, d51750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1506 q = 1) : d51751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1506, d51751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1506, d51751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1507 q = 1) : d51752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1507, d51752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1507, d51752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1508 q = 1) : d51753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1508, d51753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1508, d51753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1733 (p : Pattern) (selected : d58165 p = 1) : d58365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58160 q = 1) : d58360 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58160, d58360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58160, d58360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1732 q selected
  have h2 (q : Pattern) (selected : d58161 q = 1) : d58361 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58161, d58361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58161, d58361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58162 q = 1) : d58362 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58162, d58362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58162, d58362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58163 q = 1) : d58363 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58163, d58363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58163, d58363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58164 q = 1) : d58364 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58164, d58364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58164, d58364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58165 q = 1) : d58365 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58165, d58365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58165, d58365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1734 (p : Pattern) (selected : d1985 p = 1) : d51781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1970 q = 1) : d4550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1970, d4550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1970, d4550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro138 q selected
  have h2 (q : Pattern) (selected : d1981 q = 1) : d1981 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1982 q = 1) : d51778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1982, d51778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1982, d51778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1983 q = 1) : d51779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1983, d51779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1983, d51779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1984 q = 1) : d51780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1984, d51780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1984, d51780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1985 q = 1) : d51781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1985, d51781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1985, d51781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1735 (p : Pattern) (selected : d58174 p = 1) : d58374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58169 q = 1) : d58369 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58169, d58369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58169, d58369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1734 q selected
  have h2 (q : Pattern) (selected : d58170 q = 1) : d58370 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58170, d58370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58170, d58370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58171 q = 1) : d58371 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58171, d58371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58171, d58371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58172 q = 1) : d58372 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58172, d58372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58172, d58372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58173 q = 1) : d58373 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58173, d58373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58173, d58373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58174 q = 1) : d58374 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58174, d58374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58174, d58374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1736 (p : Pattern) (selected : d2463 p = 1) : d51810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2448 q = 1) : d4591 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2448, d4591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2448, d4591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro175 q selected
  have h2 (q : Pattern) (selected : d2459 q = 1) : d2459 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2460 q = 1) : d51807 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2460, d51807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2460, d51807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2461 q = 1) : d51808 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2461, d51808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2461, d51808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2462 q = 1) : d51809 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2462, d51809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2462, d51809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2463 q = 1) : d51810 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2463, d51810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2463, d51810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1737 (p : Pattern) (selected : d58184 p = 1) : d58384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58179 q = 1) : d58379 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58179, d58379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58179, d58379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1736 q selected
  have h2 (q : Pattern) (selected : d58180 q = 1) : d58380 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58180, d58380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58180, d58380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58181 q = 1) : d58381 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58181, d58381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58181, d58381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58182 q = 1) : d58382 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58182, d58382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58182, d58382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58183 q = 1) : d58383 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58183, d58383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58183, d58383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58184 q = 1) : d58384 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58184, d58384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58184, d58384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1738 (p : Pattern) (selected : d58190 p = 1) : d58390 p = 1 := by
  have h0 (q : Pattern) (selected : d58151 q = 1) : d58351 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58151, d58351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1727 q selected
    | true =>
      simp only [d58151, d58351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1729 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58158 q = 1) : d58358 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58158, d58358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58158, d58358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1731 q selected
  have h3 (q : Pattern) (selected : d58159 q = 1) : d58359 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58159, d58359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58159, d58359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58166 q = 1) : d58366 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58166, d58366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58166, d58366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1733 q selected
  have h5 (q : Pattern) (selected : d58167 q = 1) : d58367 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58167, d58367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58167, d58367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58168 q = 1) : d58368 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58168, d58368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58168, d58368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58175 q = 1) : d58375 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58175, d58375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58175, d58375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1735 q selected
  have h8 (q : Pattern) (selected : d58176 q = 1) : d58376 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58176, d58376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58176, d58376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58177 q = 1) : d58377 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58177, d58377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58177, d58377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58178 q = 1) : d58378 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58178, d58378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58178, d58378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58185 q = 1) : d58385 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58185, d58385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58185, d58385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1737 q selected
  have h12 (q : Pattern) (selected : d58186 q = 1) : d58386 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58186, d58386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58186, d58386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58187 q = 1) : d58387 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58187, d58387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58187, d58387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58188 q = 1) : d58388 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58188, d58388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58188, d58388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58189 q = 1) : d58389 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58189, d58389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58189, d58389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d58190 q = 1) : d58390 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58190, d58390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58190, d58390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1739 (p : Pattern) (selected : d58196 p = 1) : d58396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58191 q = 1) : d58391 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58191, d58391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1738 q selected
    | true =>
      simp only [d58191, d58391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58192 q = 1) : d58392 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58192, d58392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58192, d58392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58193 q = 1) : d58393 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58193, d58393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58193, d58393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58194 q = 1) : d58394 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58194, d58394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58194, d58394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58195 q = 1) : d58395 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58195, d58395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58195, d58395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58196 q = 1) : d58396 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58196, d58396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58196, d58396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1740 (p : Pattern) (selected : d58202 p = 1) : d58402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58197 q = 1) : d58397 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58197, d58397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1739 q selected
    | true =>
      simp only [d58197, d58397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58198 q = 1) : d58398 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58198, d58398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58198, d58398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58199 q = 1) : d58399 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58199, d58399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58199, d58399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58200 q = 1) : d58400 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58200, d58400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58200, d58400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58201 q = 1) : d58401 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58201, d58401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58201, d58401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58202 q = 1) : d58402 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58202, d58402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58202, d58402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1741 (p : Pattern) (selected : d58208 p = 1) : d58408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58203 q = 1) : d58403 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58203, d58403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1740 q selected
    | true =>
      simp only [d58203, d58403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58204 q = 1) : d58404 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58204, d58404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58204, d58404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58205 q = 1) : d58405 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58205, d58405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58205, d58405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58206 q = 1) : d58406 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58206, d58406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58206, d58406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58207 q = 1) : d58407 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58207, d58407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58207, d58407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58208 q = 1) : d58408 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58208, d58408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58208, d58408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1742 (p : Pattern) (selected : d58214 p = 1) : d58414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58209 q = 1) : d58409 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58209, d58409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1741 q selected
    | true =>
      simp only [d58209, d58409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58210 q = 1) : d58410 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58210, d58410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58210, d58410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58211 q = 1) : d58411 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58211, d58411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58211, d58411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58212 q = 1) : d58412 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58212, d58412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58212, d58412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58213 q = 1) : d58413 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58213, d58413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58213, d58413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58214 q = 1) : d58414 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58214, d58414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58214, d58414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1743 (p : Pattern) (selected : d58220 p = 1) : d58420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58215 q = 1) : d58415 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58215, d58415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1742 q selected
    | true =>
      simp only [d58215, d58415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58216 q = 1) : d58416 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58216, d58416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58216, d58416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58217 q = 1) : d58417 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58217, d58417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58217, d58417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58218 q = 1) : d58418 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58218, d58418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58218, d58418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58219 q = 1) : d58419 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58219, d58419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58219, d58419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58220 q = 1) : d58420 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58220, d58420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58220, d58420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1744 (p : Pattern) (selected : d58225 p = 1) : d58425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58221 q = 1) : d58421 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58221, d58421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1743 q selected
    | true =>
      simp only [d58221, d58421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58222 q = 1) : d58422 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58222, d58422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58222, d58422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58223 q = 1) : d58423 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58223, d58423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58223, d58423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58224 q = 1) : d58424 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58224, d58424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58224, d58424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58225 q = 1) : d58425 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58225, d58425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58225, d58425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1745 (p : Pattern) (selected : d58231 p = 1) : d58431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58226 q = 1) : d58426 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58226, d58426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1744 q selected
    | true =>
      simp only [d58226, d58426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58227 q = 1) : d58427 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58227, d58427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58227, d58427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58228 q = 1) : d58428 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58228, d58428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58228, d58428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58229 q = 1) : d58429 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58229, d58429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58229, d58429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d58230 q = 1) : d58430 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58230, d58430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58230, d58430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58231 q = 1) : d58431 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58231, d58431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58231, d58431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1746 (p : Pattern) (selected : d3147 p = 0) : d58438 p = 1 := by
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
  have h6 (q : Pattern) (selected : d212 q = 0) : d52030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro214 q selected
    | true =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro219 q selected
  have h7 (q : Pattern) (selected : d3143 q = 0) : d58434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3143, d58434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3143, d58434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3144 q = 0) : d58435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3144, d58435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3144, d58435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3145 q = 0) : d58436 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3145, d58436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3145, d58436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d221 q = 0) : d52039 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d52039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d221, d52039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro221 q selected
  have h11 (q : Pattern) (selected : d222 q = 0) : d52040 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d52040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222, d52040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223 q = 0) : d52041 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d52041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223, d52041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d224 q = 0) : d52042 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d52042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d224, d52042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3146 q = 0) : d58437 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3146, d58437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3146, d58437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d269 q = 0) : d52068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269, d52068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d269, d52068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro228 q selected
  have h16 (q : Pattern) (selected : d270 q = 0) : d52069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270, d52069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d270, d52069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d271 q = 0) : d52070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271, d52070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d271, d52070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d272 q = 0) : d52071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d272, d52071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d272, d52071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d273 q = 0) : d52072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273, d52072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d273, d52072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3147 q = 0) : d58438 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3147, d58438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3147, d58438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1747 (p : Pattern) (selected : d3164 p = 0) : d58455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d285 q = 0) : d52084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro230 q selected
  have h2 (q : Pattern) (selected : d286 q = 0) : d52085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292 q = 0) : d52091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro230 q selected
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro231 q selected
  have h4 (q : Pattern) (selected : d293 q = 0) : d52092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d294 q = 0) : d52093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d396 q = 0) : d52162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro244 q selected
    | true =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro249 q selected
  have h7 (q : Pattern) (selected : d3153 q = 0) : d58444 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3153, d58444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3153, d58444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3154 q = 0) : d58445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3154, d58445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3154, d58445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3155 q = 0) : d58446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3155, d58446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3155, d58446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d405 q = 0) : d52171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d52171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d405, d52171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro251 q selected
  have h11 (q : Pattern) (selected : d3156 q = 0) : d58447 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3156, d58447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3156, d58447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3157 q = 0) : d58448 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3157, d58448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3157, d58448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3158 q = 0) : d58449 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3158, d58449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3158, d58449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3159 q = 0) : d58450 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3159, d58450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3159, d58450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d457 q = 0) : d52204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d457, d52204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d457, d52204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro259 q selected
  have h16 (q : Pattern) (selected : d3160 q = 0) : d58451 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3160, d58451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3160, d58451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3161 q = 0) : d58452 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3161, d58452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3161, d58452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3162 q = 0) : d58453 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3162, d58453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3162, d58453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3163 q = 0) : d58454 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3163, d58454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3163, d58454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3164 q = 0) : d58455 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3164, d58455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3164, d58455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1748 (p : Pattern) (selected : d3170 p = 0) : d58461 p = 1 := by
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
  have h5 (q : Pattern) (selected : d3148 q = 0) : d58439 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3148, d58439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3148, d58439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1746 q selected
  have h6 (q : Pattern) (selected : d3149 q = 0) : d58440 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3149, d58440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3149, d58440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3150 q = 0) : d58441 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3150, d58441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3150, d58441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3151 q = 0) : d58442 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3151, d58442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3151, d58442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3152 q = 0) : d58443 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3152, d58443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3152, d58443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3165 q = 0) : d58456 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3165, d58456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3165, d58456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1747 q selected
  have h11 (q : Pattern) (selected : d3166 q = 0) : d58457 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3166, d58457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3166, d58457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3167 q = 0) : d58458 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3167, d58458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3167, d58458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3168 q = 0) : d58459 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3168, d58459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3168, d58459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3169 q = 0) : d58460 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3169, d58460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3169, d58460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3170 q = 0) : d58461 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3170, d58461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3170, d58461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1749 (p : Pattern) (selected : d3182 p = 0) : d58473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d498 q = 0) : d52245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro267 q selected
  have h2 (q : Pattern) (selected : d499 q = 0) : d52246 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d508 q = 0) : d52255 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro267 q selected
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro270 q selected
  have h4 (q : Pattern) (selected : d509 q = 0) : d52256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d510 q = 0) : d52257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d632 q = 0) : d52336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro288 q selected
    | true =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro296 q selected
  have h7 (q : Pattern) (selected : d3171 q = 0) : d58462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3171, d58462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3171, d58462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3172 q = 0) : d58463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3172, d58463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3172, d58463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3173 q = 0) : d58464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3173, d58464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3173, d58464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d652 q = 0) : d52356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d52356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d652, d52356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro299 q selected
  have h11 (q : Pattern) (selected : d3174 q = 0) : d58465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3174, d58465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3174, d58465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3175 q = 0) : d58466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3175, d58466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3175, d58466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3176 q = 0) : d58467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3176, d58467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3176, d58467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3177 q = 0) : d58468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3177, d58468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3177, d58468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d726 q = 0) : d52407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d726, d52407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d726, d52407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro312 q selected
  have h16 (q : Pattern) (selected : d3178 q = 0) : d58469 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3178, d58469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3178, d58469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3179 q = 0) : d58470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3179, d58470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3179, d58470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3180 q = 0) : d58471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3180, d58471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3180, d58471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3181 q = 0) : d58472 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3181, d58472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3181, d58472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3182 q = 0) : d58473 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3182, d58473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3182, d58473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
end NetHack.Soko22Hazard87
