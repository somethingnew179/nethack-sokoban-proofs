import NetHack.Soko22Hazard87.AndIntroBlocks0007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro2000 (p : Pattern) (ha : d62485 p = 1) (hb : d62636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62480 q = 1) (hb : d62631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62480, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62480, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1999 q ha hb
  have h2 (q : Pattern) (ha : d62481 q = 1) (hb : d62632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62481, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62481, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62482 q = 1) (hb : d62633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62482, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62482, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62483 q = 1) (hb : d62634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62483, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62483, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62484 q = 1) (hb : d62635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62484, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62484, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62485 q = 1) (hb : d62636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62485, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62485, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2001 (p : Pattern) (ha : d3613 p = 1) (hb : d62493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3613 q = 1) (hb : d62493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, d62493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3613, d62493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2002 (p : Pattern) (ha : d62491 p = 1) (hb : d62641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro301 q ha hb
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4567 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51793 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51794 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62491 q = 1) (hb : d62641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62491, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62491, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro2003 (p : Pattern) (ha : d62499 p = 1) (hb : d62647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d55685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d55686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3610 q = 1) (hb : d62490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62492 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62492, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62492, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2002 q ha hb
  have h5 (q : Pattern) (ha : d3614 q = 1) (hb : d62494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, d62494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
    | true =>
      simp only [d3614, d62494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2001 q ha hb
  have h6 (q : Pattern) (ha : d62495 q = 1) (hb : d62643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62495, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62495, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62496 q = 1) (hb : d62644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62496, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62496, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62497 q = 1) (hb : d62645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62497, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62497, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62498 q = 1) (hb : d62646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62498, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62498, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d62499 q = 1) (hb : d62647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62499, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62499, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro2004 (p : Pattern) (ha : d62505 p = 1) (hb : d62653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62500 q = 1) (hb : d62648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62500, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62500, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2003 q ha hb
  have h2 (q : Pattern) (ha : d62501 q = 1) (hb : d62649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62501, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62501, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62502 q = 1) (hb : d62650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62502, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62502, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62503 q = 1) (hb : d62651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62503, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62503, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62504 q = 1) (hb : d62652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62504, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62504, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62505 q = 1) (hb : d62653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62505, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62505, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2005 (p : Pattern) (ha : d62511 p = 1) (hb : d62659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62432 q = 1) (hb : d62592 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62432, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1984 q ha hb
    | true =>
      simp only [d62432, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1988 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62449 q = 1) (hb : d62606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62449, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62449, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1992 q ha hb
  have h3 (q : Pattern) (ha : d62450 q = 1) (hb : d62607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62450, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62450, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62467 q = 1) (hb : d62621 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62467, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62467, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1996 q ha hb
  have h5 (q : Pattern) (ha : d62468 q = 1) (hb : d62622 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62468, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62468, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62469 q = 1) (hb : d62623 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62469, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62469, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62486 q = 1) (hb : d62637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62486, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62486, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2000 q ha hb
  have h8 (q : Pattern) (ha : d62487 q = 1) (hb : d62638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62487, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62487, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62488 q = 1) (hb : d62639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62488, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62488, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62489 q = 1) (hb : d62640 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62489, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62489, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62506 q = 1) (hb : d62654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62506, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62506, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2004 q ha hb
  have h12 (q : Pattern) (ha : d62507 q = 1) (hb : d62655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62507, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62507, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62508 q = 1) (hb : d62656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62508, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62508, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62509 q = 1) (hb : d62657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62509, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62509, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62510 q = 1) (hb : d62658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62510, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62510, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62511 q = 1) (hb : d62659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62511, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62511, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2006 (p : Pattern) (ha : d62517 p = 1) (hb : d62665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62512 q = 1) (hb : d62660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62512, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2005 q ha hb
    | true =>
      simp only [d62512, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62513 q = 1) (hb : d62661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62513, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62513, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62514 q = 1) (hb : d62662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62514, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62514, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62515 q = 1) (hb : d62663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62515, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62515, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62516 q = 1) (hb : d62664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62516, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62516, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62517 q = 1) (hb : d62665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62517, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62517, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2007 (p : Pattern) (ha : d62523 p = 1) (hb : d62671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62518 q = 1) (hb : d62666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62518, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2006 q ha hb
    | true =>
      simp only [d62518, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62519 q = 1) (hb : d62667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62519, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62519, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62520 q = 1) (hb : d62668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62520, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62520, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62521 q = 1) (hb : d62669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62521, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62521, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62522 q = 1) (hb : d62670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62522, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62522, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62523 q = 1) (hb : d62671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62523, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62523, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2008 (p : Pattern) (ha : d62529 p = 1) (hb : d62677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62524 q = 1) (hb : d62672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62524, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2007 q ha hb
    | true =>
      simp only [d62524, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62525 q = 1) (hb : d62673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62525, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62525, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62526 q = 1) (hb : d62674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62526, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62526, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62527 q = 1) (hb : d62675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62527, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62527, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62528 q = 1) (hb : d62676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62528, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62528, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62529 q = 1) (hb : d62677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62529, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62529, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2009 (p : Pattern) (ha : d62535 p = 1) (hb : d62683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62530 q = 1) (hb : d62678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62530, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2008 q ha hb
    | true =>
      simp only [d62530, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62531 q = 1) (hb : d62679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62531, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62531, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62532 q = 1) (hb : d62680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62532, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62532, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62533 q = 1) (hb : d62681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62533, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62533, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62534 q = 1) (hb : d62682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62534, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62534, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62535 q = 1) (hb : d62683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62535, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62535, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2010 (p : Pattern) (ha : d62541 p = 1) (hb : d62689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62536 q = 1) (hb : d62684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62536, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2009 q ha hb
    | true =>
      simp only [d62536, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62537 q = 1) (hb : d62685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62537, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62537, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62538 q = 1) (hb : d62686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62538, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62538, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62539 q = 1) (hb : d62687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62539, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62539, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62540 q = 1) (hb : d62688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62540, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62540, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62541 q = 1) (hb : d62689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62541, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62541, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2011 (p : Pattern) (ha : d62547 p = 1) (hb : d62695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62542 q = 1) (hb : d62690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62542, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2010 q ha hb
    | true =>
      simp only [d62542, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62543 q = 1) (hb : d62691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62543, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62543, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62544 q = 1) (hb : d62692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62544, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62544, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62545 q = 1) (hb : d62693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62545, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62545, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62546 q = 1) (hb : d62694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62546, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62546, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62547 q = 1) (hb : d62695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62547, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62547, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2012 (p : Pattern) (ha : d62553 p = 1) (hb : d62701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62548 q = 1) (hb : d62696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62548, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2011 q ha hb
    | true =>
      simp only [d62548, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62549 q = 1) (hb : d62697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62549, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62549, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62550 q = 1) (hb : d62698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62550, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62550, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62551 q = 1) (hb : d62699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62551, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62551, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62552 q = 1) (hb : d62700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62552, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62552, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62553 q = 1) (hb : d62701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62553, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62553, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2013 (p : Pattern) (ha : d54404 p = 1) (hb : d62376 p = 1) : d62704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d54978 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d54978 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d54978 q = 1) : d2527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d54978 q = 1) : d62702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d407 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d62375 q = 1) : d62703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d62375, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, d62375, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54404 q = 1) (hb : d62376 q = 1) : d62704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d62376, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54404, d62376, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2014 (p : Pattern) (ha : d54410 p = 1) (hb : d62376 p = 1) : d62712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d54978 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d54978 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d54978 q = 1) : d2539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d54978 q = 1) : d62710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53655 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53656 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53657 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53658 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53659 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53660 q = 1) (hb : d62375 q = 1) : d62711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d62375, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d62375, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54410 q = 1) (hb : d62376 q = 1) : d62712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d62376, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54410, d62376, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2015 (p : Pattern) (ha : d54416 p = 1) (hb : d62376 p = 1) : d62718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54405 q = 1) (hb : d62376 q = 1) : d62705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54405, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2013 q ha hb
  have h2 (q : Pattern) (ha : d54406 q = 1) (hb : d62376 q = 1) : d62706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54406, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54407 q = 1) (hb : d62376 q = 1) : d62707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54407, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54408 q = 1) (hb : d62376 q = 1) : d62708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54408, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54409 q = 1) (hb : d62376 q = 1) : d62709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54411 q = 1) (hb : d62376 q = 1) : d62713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54411, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2014 q ha hb
  have h7 (q : Pattern) (ha : d54412 q = 1) (hb : d62376 q = 1) : d62714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54412, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54413 q = 1) (hb : d62376 q = 1) : d62715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54413, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54414 q = 1) (hb : d62376 q = 1) : d62716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54414, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54415 q = 1) (hb : d62376 q = 1) : d62717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54415, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54416 q = 1) (hb : d62376 q = 1) : d62718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54416, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2016 (p : Pattern) (ha : d54417 p = 1) (hb : d62376 p = 1) : d62721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d54978 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d54978 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d54978 q = 1) : d2552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d54978 q = 1) : d62719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53680 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53681 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53682 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53683 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53684 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53685 q = 1) (hb : d62375 q = 1) : d62720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d62375, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d62375, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54417 q = 1) (hb : d62376 q = 1) : d62721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d62376, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54417, d62376, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2017 (p : Pattern) (ha : d54423 p = 1) (hb : d62376 p = 1) : d62727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d62376 q = 1) : d62722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2016 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d62376 q = 1) : d62723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d62376 q = 1) : d62724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d62376 q = 1) : d62725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d62376 q = 1) : d62726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d62376 q = 1) : d62727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2018 (p : Pattern) (ha : d54425 p = 1) (hb : d62376 p = 1) : d62731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d54978 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d54978 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d54978 q = 1) : d2566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d54978 q = 1) : d62729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53707 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53708 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53709 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53710 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53711 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53712 q = 1) (hb : d62375 q = 1) : d62730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d62375, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d62375, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54425 q = 1) (hb : d62376 q = 1) : d62731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d62376, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54425, d62376, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2019 (p : Pattern) (ha : d54431 p = 1) (hb : d62376 p = 1) : d62737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d62376 q = 1) : d62732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2018 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d62376 q = 1) : d62733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d62376 q = 1) : d62734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d62376 q = 1) : d62735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d62376 q = 1) : d62736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d62376 q = 1) : d62737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2020 (p : Pattern) (ha : d54434 p = 1) (hb : d62376 p = 1) : d62742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d54978 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d54978 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d54978 q = 1) : d2581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d54978 q = 1) : d62740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53735 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53736 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53737 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53738 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53739 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53740 q = 1) (hb : d62375 q = 1) : d62741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d62375, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d62375, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54434 q = 1) (hb : d62376 q = 1) : d62742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54434, d62376, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54434, d62376, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2021 (p : Pattern) (ha : d54440 p = 1) (hb : d62376 p = 1) : d62748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54435 q = 1) (hb : d62376 q = 1) : d62743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54435, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54435, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2020 q ha hb
  have h2 (q : Pattern) (ha : d54436 q = 1) (hb : d62376 q = 1) : d62744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54436, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54436, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54437 q = 1) (hb : d62376 q = 1) : d62745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54437, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54437, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54438 q = 1) (hb : d62376 q = 1) : d62746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54438, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54438, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54439 q = 1) (hb : d62376 q = 1) : d62747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54439, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54439, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54440 q = 1) (hb : d62376 q = 1) : d62748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54440, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54440, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2022 (p : Pattern) (ha : d54444 p = 1) (hb : d62376 p = 1) : d62754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d54978 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d54978 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d54978 q = 1) : d2597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d54978 q = 1) : d62752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53765 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53766 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53767 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53768 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53769 q = 1) (hb : d62375 q = 1) : d62753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d62375, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d62375, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54444 q = 1) (hb : d62376 q = 1) : d62754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54444, d62376, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54444, d62376, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2023 (p : Pattern) (ha : d54450 p = 1) (hb : d62376 p = 1) : d62760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54445 q = 1) (hb : d62376 q = 1) : d62755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54445, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54445, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2022 q ha hb
  have h2 (q : Pattern) (ha : d54446 q = 1) (hb : d62376 q = 1) : d62756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54446, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54446, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54447 q = 1) (hb : d62376 q = 1) : d62757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54447, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54447, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54448 q = 1) (hb : d62376 q = 1) : d62758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54448, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54448, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54449 q = 1) (hb : d62376 q = 1) : d62759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54449, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54449, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54450 q = 1) (hb : d62376 q = 1) : d62760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54450, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54450, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2024 (p : Pattern) (ha : d54455 p = 1) (hb : d62376 p = 1) : d62767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d54978 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d54978 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d54978 q = 1) : d2614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d54978 q = 1) : d62765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53794 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53795 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53796 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53797 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d53798 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d53799 q = 1) (hb : d62375 q = 1) : d62766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d62375, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d62375, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d54455 q = 1) (hb : d62376 q = 1) : d62767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54455, d62376, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54455, d62376, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2025 (p : Pattern) (ha : d54461 p = 1) (hb : d62376 p = 1) : d62773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54456 q = 1) (hb : d62376 q = 1) : d62768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54456, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54456, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2024 q ha hb
  have h2 (q : Pattern) (ha : d54457 q = 1) (hb : d62376 q = 1) : d62769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54457, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54457, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54458 q = 1) (hb : d62376 q = 1) : d62770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54458, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54458, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54459 q = 1) (hb : d62376 q = 1) : d62771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54459, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54459, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54460 q = 1) (hb : d62376 q = 1) : d62772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54460, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54460, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54461 q = 1) (hb : d62376 q = 1) : d62773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54461, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54461, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2026 (p : Pattern) (ha : d54467 p = 1) (hb : d62376 p = 1) : d62779 p = 1 := by
  have h0 (q : Pattern) (ha : d54424 q = 1) (hb : d62376 q = 1) : d62728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54424, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2015 q ha hb
    | true =>
      simp only [d54424, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2017 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54432 q = 1) (hb : d62376 q = 1) : d62738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54432, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54432, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2019 q ha hb
  have h3 (q : Pattern) (ha : d54433 q = 1) (hb : d62376 q = 1) : d62739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54433, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54433, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54441 q = 1) (hb : d62376 q = 1) : d62749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54441, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54441, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2021 q ha hb
  have h5 (q : Pattern) (ha : d54442 q = 1) (hb : d62376 q = 1) : d62750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54442, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54442, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54443 q = 1) (hb : d62376 q = 1) : d62751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54443, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54443, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54451 q = 1) (hb : d62376 q = 1) : d62761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54451, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54451, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2023 q ha hb
  have h8 (q : Pattern) (ha : d54452 q = 1) (hb : d62376 q = 1) : d62762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54452, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54452, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54453 q = 1) (hb : d62376 q = 1) : d62763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54453, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54453, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54454 q = 1) (hb : d62376 q = 1) : d62764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54454, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54454, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54462 q = 1) (hb : d62376 q = 1) : d62774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54462, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54462, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2025 q ha hb
  have h12 (q : Pattern) (ha : d54463 q = 1) (hb : d62376 q = 1) : d62775 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54463, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54463, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54464 q = 1) (hb : d62376 q = 1) : d62776 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54464, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54464, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54465 q = 1) (hb : d62376 q = 1) : d62777 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54465, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54465, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54466 q = 1) (hb : d62376 q = 1) : d62778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54466, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54466, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54467 q = 1) (hb : d62376 q = 1) : d62779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54467, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54467, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2027 (p : Pattern) (ha : d54473 p = 1) (hb : d62376 p = 1) : d62785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54468 q = 1) (hb : d62376 q = 1) : d62780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54468, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2026 q ha hb
    | true =>
      simp only [d54468, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54469 q = 1) (hb : d62376 q = 1) : d62781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54469, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54469, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54470 q = 1) (hb : d62376 q = 1) : d62782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54470, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54470, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54471 q = 1) (hb : d62376 q = 1) : d62783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54471, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54471, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54472 q = 1) (hb : d62376 q = 1) : d62784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54472, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54472, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54473 q = 1) (hb : d62376 q = 1) : d62785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54473, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54473, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2028 (p : Pattern) (ha : d54479 p = 1) (hb : d62376 p = 1) : d62791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54474 q = 1) (hb : d62376 q = 1) : d62786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54474, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2027 q ha hb
    | true =>
      simp only [d54474, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54475 q = 1) (hb : d62376 q = 1) : d62787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54475, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54475, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54476 q = 1) (hb : d62376 q = 1) : d62788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54476, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54476, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54477 q = 1) (hb : d62376 q = 1) : d62789 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54477, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54477, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54478 q = 1) (hb : d62376 q = 1) : d62790 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54478, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54478, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54479 q = 1) (hb : d62376 q = 1) : d62791 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54479, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54479, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2029 (p : Pattern) (ha : d54485 p = 1) (hb : d62376 p = 1) : d62797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54480 q = 1) (hb : d62376 q = 1) : d62792 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54480, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2028 q ha hb
    | true =>
      simp only [d54480, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54481 q = 1) (hb : d62376 q = 1) : d62793 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54481, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54481, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54482 q = 1) (hb : d62376 q = 1) : d62794 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54482, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54482, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54483 q = 1) (hb : d62376 q = 1) : d62795 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54483, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54483, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54484 q = 1) (hb : d62376 q = 1) : d62796 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54484, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54484, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54485 q = 1) (hb : d62376 q = 1) : d62797 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54485, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54485, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2030 (p : Pattern) (ha : d54491 p = 1) (hb : d62376 p = 1) : d62803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54486 q = 1) (hb : d62376 q = 1) : d62798 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54486, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2029 q ha hb
    | true =>
      simp only [d54486, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54487 q = 1) (hb : d62376 q = 1) : d62799 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54487, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54487, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54488 q = 1) (hb : d62376 q = 1) : d62800 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54488, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54488, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54489 q = 1) (hb : d62376 q = 1) : d62801 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54489, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54489, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54490 q = 1) (hb : d62376 q = 1) : d62802 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54490, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54490, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54491 q = 1) (hb : d62376 q = 1) : d62803 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54491, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54491, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2031 (p : Pattern) (ha : d54497 p = 1) (hb : d62376 p = 1) : d62809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54492 q = 1) (hb : d62376 q = 1) : d62804 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54492, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2030 q ha hb
    | true =>
      simp only [d54492, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54493 q = 1) (hb : d62376 q = 1) : d62805 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54493, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54493, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54494 q = 1) (hb : d62376 q = 1) : d62806 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54494, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54494, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54495 q = 1) (hb : d62376 q = 1) : d62807 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54495, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54495, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54496 q = 1) (hb : d62376 q = 1) : d62808 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54496, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54496, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54497 q = 1) (hb : d62376 q = 1) : d62809 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54497, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54497, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2032 (p : Pattern) (ha : d54503 p = 1) (hb : d62376 p = 1) : d62815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54498 q = 1) (hb : d62376 q = 1) : d62810 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54498, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2031 q ha hb
    | true =>
      simp only [d54498, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54499 q = 1) (hb : d62376 q = 1) : d62811 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54499, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54499, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54500 q = 1) (hb : d62376 q = 1) : d62812 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54500, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54500, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54501 q = 1) (hb : d62376 q = 1) : d62813 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54501, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54501, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54502 q = 1) (hb : d62376 q = 1) : d62814 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54502, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54502, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54503 q = 1) (hb : d62376 q = 1) : d62815 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54503, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54503, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2033 (p : Pattern) (ha : d54509 p = 1) (hb : d62376 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54504 q = 1) (hb : d62376 q = 1) : d62816 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54504, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2032 q ha hb
    | true =>
      simp only [d54504, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54505 q = 1) (hb : d62376 q = 1) : d62817 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54505, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54505, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54506 q = 1) (hb : d62376 q = 1) : d62818 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54506, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54506, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54507 q = 1) (hb : d62376 q = 1) : d62819 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54507, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54507, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54508 q = 1) (hb : d62376 q = 1) : d62820 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54508, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54508, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54509 q = 1) (hb : d62376 q = 1) : d62821 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54509, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54509, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2034 (p : Pattern) (ha : d213 p = 1) (hb : d62389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d213 q = 1) (hb : d62389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d62389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d213, d62389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h10 p ha hb
theorem andIntro2035 (p : Pattern) (ha : d62395 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d62390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d62390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d62390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2034 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d62391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d62391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d62391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2527 q = 1) (hb : d62392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d62392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d62392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62393 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62393, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62393, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62394 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62394, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62394, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62395 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62395, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62395, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2036 (p : Pattern) (ha : d2536 p = 1) (hb : d62402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d62402 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d62402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, d62402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2037 (p : Pattern) (ha : d62409 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d62403 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d62403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d62403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2036 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62404 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d62405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d62405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d62405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2539 q = 1) (hb : d62406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d62406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d62406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62407 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62407, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62407, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62408 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62408, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62408, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62409 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62409, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62409, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2038 (p : Pattern) (ha : d62415 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62396 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62396, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62396, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2035 q ha hb
  have h3 (q : Pattern) (ha : d62397 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62397, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62397, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62398 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62398, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62398, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62399 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62399, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62399, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62400 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62400, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62400, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62410 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62410, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62410, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2037 q ha hb
  have h8 (q : Pattern) (ha : d62411 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62411, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62411, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62412 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62412, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62412, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62413 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62413, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62413, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62414 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62414, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62414, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62415 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62415, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62415, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2039 (p : Pattern) (ha : d2549 p = 1) (hb : d62417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d62417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d62417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, d62417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2040 (p : Pattern) (ha : d62425 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d62418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d62418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d62418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2039 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62420 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d62421 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d62421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d62421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2552 q = 1) (hb : d62422 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d62422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d62422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62423 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62423, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62423, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62424 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62424, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62424, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62425 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62425, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62425, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2041 (p : Pattern) (ha : d62431 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62426 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62426, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62426, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2040 q ha hb
  have h2 (q : Pattern) (ha : d62427 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62427, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62427, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62428 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62428, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62428, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62429 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62429, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62429, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62430 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62430, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62430, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62431 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62431, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62431, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2042 (p : Pattern) (ha : d2563 p = 1) (hb : d62434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d62434 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d62434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, d62434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2043 (p : Pattern) (ha : d62442 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62433 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d62435 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d62435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d62435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2042 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62437 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d62438 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d62438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d62438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2566 q = 1) (hb : d62439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d62439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d62439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62440 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62440, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62440, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62441 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62441, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62441, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62442 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62442, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62442, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2044 (p : Pattern) (ha : d62448 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62443 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62443, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62443, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2043 q ha hb
  have h2 (q : Pattern) (ha : d62444 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62444, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62444, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62445 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62445, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62445, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62446 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62446, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62446, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62447 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62447, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62447, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62448 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62448, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62448, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2045 (p : Pattern) (ha : d2578 p = 1) (hb : d62452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d62452 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d62452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, d62452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2046 (p : Pattern) (ha : d62460 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d62453 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d62453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d62453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2045 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62455 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d62456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d62456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d62456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2581 q = 1) (hb : d62457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d62457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d62457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62458 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62458, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62458, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62459 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62459, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62459, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62460 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62460, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62460, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2047 (p : Pattern) (ha : d62466 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62461 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62461, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62461, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2046 q ha hb
  have h2 (q : Pattern) (ha : d62462 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62462, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62462, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62463 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62463, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62463, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62464 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62464, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62464, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62465 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62465, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62465, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62466 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62466, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62466, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2048 (p : Pattern) (ha : d2594 p = 1) (hb : d62471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d62471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d62471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, d62471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2049 (p : Pattern) (ha : d62479 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62470 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d62472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d62472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d62472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2048 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d62475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d62475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d62475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2597 q = 1) (hb : d62476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d62476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d62476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62477 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62477, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62477, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62478 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62478, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62478, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62479 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62479, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62479, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2050 (p : Pattern) (ha : d62485 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62480 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62480, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62480, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2049 q ha hb
  have h2 (q : Pattern) (ha : d62481 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62481, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62481, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62482 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62482, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62482, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62483 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62483, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62483, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62484 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62484, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62484, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62485 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62485, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62485, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2051 (p : Pattern) (ha : d2611 p = 1) (hb : d62491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d62491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d62491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, d62491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2052 (p : Pattern) (ha : d62499 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62490 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d62492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d62492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d62492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2051 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62494 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d62495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d62495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d62495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2614 q = 1) (hb : d62496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d62496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d62496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62497 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62497, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62497, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62498 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62498, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62498, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d62499 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62499, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62499, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2053 (p : Pattern) (ha : d62505 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62500 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62500, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62500, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2052 q ha hb
  have h2 (q : Pattern) (ha : d62501 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62501, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62501, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62502 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62502, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62502, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62503 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62503, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62503, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62504 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62504, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62504, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62505 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62505, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62505, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2054 (p : Pattern) (ha : d62511 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62432 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62432, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2038 q ha hb
    | true =>
      simp only [d62432, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2041 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62449 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62449, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62449, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2044 q ha hb
  have h3 (q : Pattern) (ha : d62450 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62450, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62450, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62467 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62467, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62467, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2047 q ha hb
  have h5 (q : Pattern) (ha : d62468 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62468, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62468, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62469 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62469, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62469, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62486 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62486, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62486, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2050 q ha hb
  have h8 (q : Pattern) (ha : d62487 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62487, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62487, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62488 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62488, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62488, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62489 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62489, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62489, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62506 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62506, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62506, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2053 q ha hb
  have h12 (q : Pattern) (ha : d62507 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62507, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62507, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62508 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62508, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62508, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62509 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62509, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62509, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62510 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62510, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62510, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62511 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62511, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62511, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2055 (p : Pattern) (ha : d62517 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62512 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62512, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2054 q ha hb
    | true =>
      simp only [d62512, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62513 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62513, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62513, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62514 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62514, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62514, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62515 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62515, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62515, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62516 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62516, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62516, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62517 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62517, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62517, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2056 (p : Pattern) (ha : d62523 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62518 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62518, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2055 q ha hb
    | true =>
      simp only [d62518, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62519 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62519, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62519, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62520 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62520, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62520, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62521 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62521, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62521, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62522 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62522, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62522, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62523 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62523, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62523, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2057 (p : Pattern) (ha : d62529 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62524 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62524, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2056 q ha hb
    | true =>
      simp only [d62524, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62525 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62525, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62525, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62526 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62526, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62526, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62527 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62527, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62527, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62528 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62528, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62528, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62529 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62529, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62529, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2058 (p : Pattern) (ha : d62535 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62530 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62530, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2057 q ha hb
    | true =>
      simp only [d62530, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62531 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62531, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62531, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62532 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62532, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62532, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62533 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62533, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62533, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62534 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62534, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62534, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62535 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62535, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62535, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2059 (p : Pattern) (ha : d62541 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62536 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62536, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2058 q ha hb
    | true =>
      simp only [d62536, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62537 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62537, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62537, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62538 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62538, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62538, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62539 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62539, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62539, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62540 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62540, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62540, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62541 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62541, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62541, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2060 (p : Pattern) (ha : d62547 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62542 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62542, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2059 q ha hb
    | true =>
      simp only [d62542, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62543 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62543, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62543, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62544 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62544, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62544, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62545 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62545, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62545, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62546 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62546, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62546, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62547 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62547, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62547, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2061 (p : Pattern) (ha : d62553 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62548 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62548, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2060 q ha hb
    | true =>
      simp only [d62548, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62549 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62549, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62549, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62550 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62550, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62550, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62551 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62551, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62551, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62552 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62552, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62552, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62553 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62553, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62553, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2062 (p : Pattern) (ha : d213 p = 1) (hb : d62554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d4336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d51641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d213 q = 1) (hb : d62554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d213, d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2063 (p : Pattern) (ha : d62560 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3508 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d62555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2062 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d62556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2527 q = 1) (hb : d62557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62558 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62558, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62559 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62559, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62560 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62560, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2064 (p : Pattern) (ha : d2536 p = 1) (hb : d62566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d4372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d51658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d62566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2065 (p : Pattern) (ha : d62572 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3521 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d62567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2064 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3524 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d62568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2539 q = 1) (hb : d62569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62570 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62570, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62571 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62571, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62572 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62572, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2066 (p : Pattern) (ha : d62578 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62561 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62561, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2063 q ha hb
  have h3 (q : Pattern) (ha : d62562 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62562, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62563 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62563, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62564 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62564, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62565 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62565, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62573 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62573, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2065 q ha hb
  have h8 (q : Pattern) (ha : d62574 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62574, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62575 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62575, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62576 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62576, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62577 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62577, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62578 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62578, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2067 (p : Pattern) (ha : d2549 p = 1) (hb : d62579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d4409 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d51683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d62579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2068 (p : Pattern) (ha : d62585 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3536 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d62580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2067 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3540 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d62581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2552 q = 1) (hb : d62582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62583 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62583, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62584 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62584, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62585 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62585, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2069 (p : Pattern) (ha : d62591 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62586 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62586, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2068 q ha hb
  have h2 (q : Pattern) (ha : d62587 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62587, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62588 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62588, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62589 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62589, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62590 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62590, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62591 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62591, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2070 (p : Pattern) (ha : d2563 p = 1) (hb : d62593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d4447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d51709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d62593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2071 (p : Pattern) (ha : d62599 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3553 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d62594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2070 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3557 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d62595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2566 q = 1) (hb : d62596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62597 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62597, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62598 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62598, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62599 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62599, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2072 (p : Pattern) (ha : d62605 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62600 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62600, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2071 q ha hb
  have h2 (q : Pattern) (ha : d62601 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62601, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62602 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62602, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62603 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62603, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62604 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62604, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62605 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62605, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2073 (p : Pattern) (ha : d2578 p = 1) (hb : d62608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d4486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d51736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d62608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2074 (p : Pattern) (ha : d62614 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3571 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d62609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2073 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d62610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2581 q = 1) (hb : d62611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62612 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62612, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62613 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62613, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62614 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62614, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2075 (p : Pattern) (ha : d62620 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62615 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62615, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2074 q ha hb
  have h2 (q : Pattern) (ha : d62616 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62616, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62617 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62617, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62618 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62618, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62619 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62619, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62620 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62620, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2076 (p : Pattern) (ha : d2594 p = 1) (hb : d62624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d4526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d51764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d62624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2077 (p : Pattern) (ha : d62630 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d62625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2076 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3594 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d62626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2597 q = 1) (hb : d62627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62628 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62628, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62629 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62629, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62630 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62630, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2078 (p : Pattern) (ha : d62636 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62631 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62631, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2077 q ha hb
  have h2 (q : Pattern) (ha : d62632 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62632, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62633 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62633, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62634 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62634, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62635 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62635, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62636 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62636, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2079 (p : Pattern) (ha : d2611 p = 1) (hb : d62641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d4567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d51793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d62641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2080 (p : Pattern) (ha : d62647 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2079 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d62643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2614 q = 1) (hb : d62644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d62645 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62645, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62646 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62646, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d62647 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62647, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2081 (p : Pattern) (ha : d62653 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62648 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62648, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2080 q ha hb
  have h2 (q : Pattern) (ha : d62649 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62649, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62650 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62650, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62651 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62651, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62652 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62652, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62653 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62653, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2082 (p : Pattern) (ha : d62659 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62592 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2066 q ha hb
    | true =>
      simp only [d62592, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2069 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62606 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62606, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2072 q ha hb
  have h3 (q : Pattern) (ha : d62607 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62621 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62621, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2075 q ha hb
  have h5 (q : Pattern) (ha : d62622 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62622, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62623 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62637 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62637, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2078 q ha hb
  have h8 (q : Pattern) (ha : d62638 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62638, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62639 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62639, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62640 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62654 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62654, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2081 q ha hb
  have h12 (q : Pattern) (ha : d62655 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62655, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62656 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62656, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62657 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62657, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62658 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62659 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2083 (p : Pattern) (ha : d62665 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62660 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2082 q ha hb
    | true =>
      simp only [d62660, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62661 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62662 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62663 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62664 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62665 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2084 (p : Pattern) (ha : d62671 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62666 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2083 q ha hb
    | true =>
      simp only [d62666, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62667 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62668 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62669 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62670 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62671 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2085 (p : Pattern) (ha : d62677 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62672 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2084 q ha hb
    | true =>
      simp only [d62672, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62673 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62674 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62675 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62676 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62677 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2086 (p : Pattern) (ha : d62683 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62678 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2085 q ha hb
    | true =>
      simp only [d62678, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62679 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62680 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62681 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62682 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62683 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2087 (p : Pattern) (ha : d62689 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62684 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2086 q ha hb
    | true =>
      simp only [d62684, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62685 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62686 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62687 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62688 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62689 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2088 (p : Pattern) (ha : d62695 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62690 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2087 q ha hb
    | true =>
      simp only [d62690, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62691 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62692 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62693 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62694 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62695 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2089 (p : Pattern) (ha : d62701 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62696 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2088 q ha hb
    | true =>
      simp only [d62696, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62697 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62698 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62699 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62700 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62701 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2090 (p : Pattern) (ha : d54298 p = 1) (hb : d62825 p = 1) : d62828 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d53867 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51647 q = 1) : d51647 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d53867 q = 1) : d58610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d53867, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51648, d53867, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d53867 q = 1) : d58611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d53867 q = 1) : d58612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4353 q = 1) (hb : d53867 q = 1) : d4353 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51651 q = 1) (hb : d53867 q = 1) : d58613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d54298 q = 1) (hb : d62825 q = 1) : d62828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d62825, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54298, d62825, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2091 (p : Pattern) (ha : d54304 p = 1) (hb : d62825 p = 1) : d62834 p = 1 := by
  have h0 (q : Pattern) (ha : d294 q = 1) (hb : d53867 q = 1) : d294 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51664 q = 1) : d51664 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51665 q = 1) (hb : d53867 q = 1) : d58620 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d53867, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51665, d53867, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51666 q = 1) (hb : d53867 q = 1) : d58621 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51666, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51667 q = 1) (hb : d53867 q = 1) : d58622 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51667, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4386 q = 1) : d4386 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51668 q = 1) (hb : d53867 q = 1) : d4387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, d53867, d4387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51668, d53867, d4387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51669 q = 1) (hb : d53867 q = 1) : d4388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51669, d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51670 q = 1) (hb : d53867 q = 1) : d4389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51670, d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51671 q = 1) (hb : d53867 q = 1) : d58623 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51671, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54304 q = 1) (hb : d62825 q = 1) : d62834 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d62825, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54304, d62825, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2092 (p : Pattern) (ha : d54310 p = 1) (hb : d62825 p = 1) : d62840 p = 1 := by
  have h0 (q : Pattern) (ha : d2676 q = 1) (hb : d62825 q = 1) : d2676 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54299 q = 1) (hb : d62825 q = 1) : d62829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54299, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2090 q ha hb
  have h3 (q : Pattern) (ha : d54300 q = 1) (hb : d62825 q = 1) : d62830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54300, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54301 q = 1) (hb : d62825 q = 1) : d62831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54301, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54302 q = 1) (hb : d62825 q = 1) : d62832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54302, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54303 q = 1) (hb : d62825 q = 1) : d62833 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54303, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54305 q = 1) (hb : d62825 q = 1) : d62835 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54305, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2091 q ha hb
  have h8 (q : Pattern) (ha : d54306 q = 1) (hb : d62825 q = 1) : d62836 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54306, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54307 q = 1) (hb : d62825 q = 1) : d62837 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54307, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54308 q = 1) (hb : d62825 q = 1) : d62838 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54308, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54309 q = 1) (hb : d62825 q = 1) : d62839 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54309, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54310 q = 1) (hb : d62825 q = 1) : d62840 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54310, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2093 (p : Pattern) (ha : d54311 p = 1) (hb : d62825 p = 1) : d62841 p = 1 := by
  have h0 (q : Pattern) (ha : d510 q = 1) (hb : d53867 q = 1) : d510 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51689 q = 1) : d51689 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51690 q = 1) (hb : d53867 q = 1) : d58631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d53867, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51690, d53867, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51691 q = 1) (hb : d53867 q = 1) : d58632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51691, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51692 q = 1) (hb : d53867 q = 1) : d58633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51692, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4423 q = 1) : d4423 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51693 q = 1) (hb : d53867 q = 1) : d4424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, d53867, d4424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51693, d53867, d4424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51694 q = 1) (hb : d53867 q = 1) : d4425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51694, d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51695 q = 1) (hb : d53867 q = 1) : d4426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51695, d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51696 q = 1) (hb : d53867 q = 1) : d58634 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51696, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54311 q = 1) (hb : d62825 q = 1) : d62841 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d62825, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54311, d62825, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2094 (p : Pattern) (ha : d54317 p = 1) (hb : d62825 p = 1) : d62847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d62825 q = 1) : d62842 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2093 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d62825 q = 1) : d62843 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d62825 q = 1) : d62844 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d62825 q = 1) : d62845 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d62825 q = 1) : d62846 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d62825 q = 1) : d62847 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2095 (p : Pattern) (ha : d54319 p = 1) (hb : d62825 p = 1) : d62849 p = 1 := by
  have h0 (q : Pattern) (ha : d802 q = 1) (hb : d53867 q = 1) : d802 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51715 q = 1) : d51715 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51716 q = 1) (hb : d53867 q = 1) : d58643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d53867, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51716, d53867, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51717 q = 1) (hb : d53867 q = 1) : d58644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51717, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51718 q = 1) (hb : d53867 q = 1) : d58645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51718, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4461 q = 1) : d4461 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51719 q = 1) (hb : d53867 q = 1) : d4462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, d53867, d4462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51719, d53867, d4462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51720 q = 1) (hb : d53867 q = 1) : d4463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51720, d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51721 q = 1) (hb : d53867 q = 1) : d4464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51721, d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51722 q = 1) (hb : d53867 q = 1) : d58646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51722, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54319 q = 1) (hb : d62825 q = 1) : d62849 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d62825, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54319, d62825, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2096 (p : Pattern) (ha : d54325 p = 1) (hb : d62825 p = 1) : d62855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d62825 q = 1) : d62850 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2095 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d62825 q = 1) : d62851 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d62825 q = 1) : d62852 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d62825 q = 1) : d62853 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d62825 q = 1) : d62854 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d62825 q = 1) : d62855 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2097 (p : Pattern) (ha : d54328 p = 1) (hb : d62825 p = 1) : d62858 p = 1 := by
  have h0 (q : Pattern) (ha : d1181 q = 1) (hb : d53867 q = 1) : d1181 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51742 q = 1) : d51742 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51743 q = 1) (hb : d53867 q = 1) : d58656 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d53867, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51743, d53867, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51744 q = 1) (hb : d53867 q = 1) : d58657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51744, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51745 q = 1) (hb : d53867 q = 1) : d58658 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51745, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4500 q = 1) : d4500 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51746 q = 1) (hb : d53867 q = 1) : d4501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, d53867, d4501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51746, d53867, d4501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51747 q = 1) (hb : d53867 q = 1) : d4502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51747, d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51748 q = 1) (hb : d53867 q = 1) : d4503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51748, d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51749 q = 1) (hb : d53867 q = 1) : d58659 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51749, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54328 q = 1) (hb : d62825 q = 1) : d62858 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d62825, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54328, d62825, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2098 (p : Pattern) (ha : d54334 p = 1) (hb : d62825 p = 1) : d62864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d62825 q = 1) : d62859 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2097 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d62825 q = 1) : d62860 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d62825 q = 1) : d62861 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d62825 q = 1) : d62862 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d62825 q = 1) : d62863 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d62825 q = 1) : d62864 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2099 (p : Pattern) (ha : d54338 p = 1) (hb : d62825 p = 1) : d62868 p = 1 := by
  have h0 (q : Pattern) (ha : d1642 q = 1) (hb : d53867 q = 1) : d1642 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51770 q = 1) : d51770 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51771 q = 1) (hb : d53867 q = 1) : d58670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d53867, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51771, d53867, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51772 q = 1) (hb : d53867 q = 1) : d58671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51772, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51773 q = 1) (hb : d53867 q = 1) : d58672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51773, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4540 q = 1) : d4540 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51774 q = 1) (hb : d53867 q = 1) : d4541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, d53867, d4541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51774, d53867, d4541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51775 q = 1) (hb : d53867 q = 1) : d4542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51775, d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51776 q = 1) (hb : d53867 q = 1) : d4543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51776, d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51777 q = 1) (hb : d53867 q = 1) : d58673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51777, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54338 q = 1) (hb : d62825 q = 1) : d62868 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d62825, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54338, d62825, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2100 (p : Pattern) (ha : d54344 p = 1) (hb : d62825 p = 1) : d62874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d62825 q = 1) : d62869 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2099 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d62825 q = 1) : d62870 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d62825 q = 1) : d62871 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d62825 q = 1) : d62872 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d62825 q = 1) : d62873 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d62825 q = 1) : d62874 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2101 (p : Pattern) (ha : d54349 p = 1) (hb : d62825 p = 1) : d62879 p = 1 := by
  have h0 (q : Pattern) (ha : d2125 q = 1) (hb : d53867 q = 1) : d2125 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d51799 q = 1) : d51799 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51800 q = 1) (hb : d53867 q = 1) : d58685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d53867, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51800, d53867, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51801 q = 1) (hb : d53867 q = 1) : d58686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51801, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51802 q = 1) (hb : d53867 q = 1) : d58687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51802, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d4581 q = 1) : d4581 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51803 q = 1) (hb : d53867 q = 1) : d4582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, d53867, d4582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51803, d53867, d4582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d51804 q = 1) (hb : d53867 q = 1) : d4583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51804, d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51805 q = 1) (hb : d53867 q = 1) : d4584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51805, d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d51806 q = 1) (hb : d53867 q = 1) : d58688 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51806, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54349 q = 1) (hb : d62825 q = 1) : d62879 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d62825, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54349, d62825, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2102 (p : Pattern) (ha : d54355 p = 1) (hb : d62825 p = 1) : d62885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d62825 q = 1) : d62880 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2101 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d62825 q = 1) : d62881 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d62825 q = 1) : d62882 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d62825 q = 1) : d62883 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d62825 q = 1) : d62884 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d62825 q = 1) : d62885 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2103 (p : Pattern) (ha : d54361 p = 1) (hb : d62825 p = 1) : d62891 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d62825 q = 1) : d62848 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2092 q ha hb
    | true =>
      simp only [d54318, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2094 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d62825 q = 1) : d62856 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2096 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d62825 q = 1) : d62857 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d62825 q = 1) : d62865 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2098 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d62825 q = 1) : d62866 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d62825 q = 1) : d62867 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d62825 q = 1) : d62875 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2100 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d62825 q = 1) : d62876 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d62825 q = 1) : d62877 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d62825 q = 1) : d62878 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d62825 q = 1) : d62886 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2102 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d62825 q = 1) : d62887 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d62825 q = 1) : d62888 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d62825 q = 1) : d62889 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d62825 q = 1) : d62890 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d62825 q = 1) : d62891 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2104 (p : Pattern) (ha : d54367 p = 1) (hb : d62825 p = 1) : d62897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d62825 q = 1) : d62892 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2103 q ha hb
    | true =>
      simp only [d54362, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d62825 q = 1) : d62893 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d62825 q = 1) : d62894 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d62825 q = 1) : d62895 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d62825 q = 1) : d62896 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d62825 q = 1) : d62897 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2105 (p : Pattern) (ha : d54373 p = 1) (hb : d62825 p = 1) : d62903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d62825 q = 1) : d62898 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2104 q ha hb
    | true =>
      simp only [d54368, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d62825 q = 1) : d62899 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d62825 q = 1) : d62900 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d62825 q = 1) : d62901 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d62825 q = 1) : d62902 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d62825 q = 1) : d62903 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2106 (p : Pattern) (ha : d54379 p = 1) (hb : d62825 p = 1) : d62909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d62825 q = 1) : d62904 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2105 q ha hb
    | true =>
      simp only [d54374, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d62825 q = 1) : d62905 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d62825 q = 1) : d62906 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d62825 q = 1) : d62907 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d62825 q = 1) : d62908 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d62825 q = 1) : d62909 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2107 (p : Pattern) (ha : d54385 p = 1) (hb : d62825 p = 1) : d62915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d62825 q = 1) : d62910 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2106 q ha hb
    | true =>
      simp only [d54380, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d62825 q = 1) : d62911 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d62825 q = 1) : d62912 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d62825 q = 1) : d62913 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d62825 q = 1) : d62914 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d62825 q = 1) : d62915 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2108 (p : Pattern) (ha : d54391 p = 1) (hb : d62825 p = 1) : d62921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d62825 q = 1) : d62916 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2107 q ha hb
    | true =>
      simp only [d54386, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d62825 q = 1) : d62917 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d62825 q = 1) : d62918 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d62825 q = 1) : d62919 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d62825 q = 1) : d62920 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d62825 q = 1) : d62921 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2109 (p : Pattern) (ha : d54397 p = 1) (hb : d62827 p = 1) : d62927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d62825 q = 1) : d62922 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2108 q ha hb
    | true =>
      simp only [d54392, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d62825 q = 1) : d62923 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d62825 q = 1) : d62924 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d62825 q = 1) : d62925 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d62826 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54396 q = 1) (hb : d62827 q = 1) : d62926 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d62827, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d62827, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54397 q = 1) (hb : d62827 q = 1) : d62927 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54397, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2110 (p : Pattern) (ha : d54403 p = 1) (hb : d62827 p = 1) : d62933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d62827 q = 1) : d62928 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2109 q ha hb
    | true =>
      simp only [d54398, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d62827 q = 1) : d62929 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d62827 q = 1) : d62930 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d62827 q = 1) : d62931 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d62827 q = 1) : d62932 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d62827 q = 1) : d62933 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2111 (p : Pattern) (ha : d58438 p = 1) (hb : d62828 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h7 (q : Pattern) (ha : d58434 q = 1) (hb : d58610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58434, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58434, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58435 q = 1) (hb : d58611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58435, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58435, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58436 q = 1) (hb : d58612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58436, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58436, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4350 q = 1) (hb : d52039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23 q ha hb
  have h11 (q : Pattern) (ha : d4351 q = 1) (hb : d52040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4352 q = 1) (hb : d52041 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4353 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58437 q = 1) (hb : d58613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58437, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58437, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58438 q = 1) (hb : d62828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58438, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58438, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2112 (p : Pattern) (ha : d58455 p = 1) (hb : d62834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h7 (q : Pattern) (ha : d58444 q = 1) (hb : d58620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58444, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58444, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58445 q = 1) (hb : d58621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58445, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58445, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58446 q = 1) (hb : d58622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58446, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58446, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4386 q = 1) (hb : d52171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46 q ha hb
  have h11 (q : Pattern) (ha : d4387 q = 1) (hb : d58447 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d58447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4387, d58447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4388 q = 1) (hb : d58448 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d58448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4388, d58448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4389 q = 1) (hb : d58449 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d58449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4389, d58449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58450 q = 1) (hb : d58623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58450, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58450, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58454 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58455 q = 1) (hb : d62834 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58455, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58455, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2113 (p : Pattern) (ha : d58461 p = 1) (hb : d62840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2673 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2673, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1821 q ha hb
  have h2 (q : Pattern) (ha : d2674 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2674, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2675 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2675, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2676 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2676, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58439 q = 1) (hb : d62829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58439, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58439, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2111 q ha hb
  have h6 (q : Pattern) (ha : d58440 q = 1) (hb : d62830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58440, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58440, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58441 q = 1) (hb : d62831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58441, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58441, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58442 q = 1) (hb : d62832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58442, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58442, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58443 q = 1) (hb : d62833 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58443, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58443, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58456 q = 1) (hb : d62835 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58456, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58456, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2112 q ha hb
  have h11 (q : Pattern) (ha : d58457 q = 1) (hb : d62836 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58457, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58457, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58458 q = 1) (hb : d62837 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58458, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58458, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58459 q = 1) (hb : d62838 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58459, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58459, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58460 q = 1) (hb : d62839 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58460, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58460, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58461 q = 1) (hb : d62840 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58461, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58461, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2114 (p : Pattern) (ha : d58473 p = 1) (hb : d62841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h7 (q : Pattern) (ha : d58462 q = 1) (hb : d58631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58462, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58462, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58463 q = 1) (hb : d58632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58463, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58463, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58464 q = 1) (hb : d58633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58464, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58464, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4423 q = 1) (hb : d52356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80 q ha hb
  have h11 (q : Pattern) (ha : d4424 q = 1) (hb : d58465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d58465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4424, d58465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4425 q = 1) (hb : d58466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d58466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4425, d58466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4426 q = 1) (hb : d58467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d58467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4426, d58467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58468 q = 1) (hb : d58634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58468, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58468, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58472 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58473 q = 1) (hb : d62841 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58473, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58473, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2115 (p : Pattern) (ha : d58479 p = 1) (hb : d62847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58474 q = 1) (hb : d62842 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58474, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58474, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2114 q ha hb
  have h2 (q : Pattern) (ha : d58475 q = 1) (hb : d62843 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58475, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58475, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58476 q = 1) (hb : d62844 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58476, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58476, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58477 q = 1) (hb : d62845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58477, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58477, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58478 q = 1) (hb : d62846 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58478, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58478, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58479 q = 1) (hb : d62847 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58479, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58479, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2116 (p : Pattern) (ha : d58492 p = 1) (hb : d62849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h7 (q : Pattern) (ha : d58481 q = 1) (hb : d58643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58481, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58481, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58482 q = 1) (hb : d58644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58482, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58482, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58483 q = 1) (hb : d58645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58483, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58483, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4461 q = 1) (hb : d52577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro126 q ha hb
  have h11 (q : Pattern) (ha : d4462 q = 1) (hb : d58484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d58484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4462, d58484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4463 q = 1) (hb : d58485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d58485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4463, d58485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4464 q = 1) (hb : d58486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d58486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4464, d58486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58487 q = 1) (hb : d58646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58487, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58487, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58491 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58492 q = 1) (hb : d62849 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58492, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58492, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2117 (p : Pattern) (ha : d58498 p = 1) (hb : d62855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58493 q = 1) (hb : d62850 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58493, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58493, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2116 q ha hb
  have h2 (q : Pattern) (ha : d58494 q = 1) (hb : d62851 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58494, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58494, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58495 q = 1) (hb : d62852 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58495, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58495, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58496 q = 1) (hb : d62853 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58496, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58496, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58497 q = 1) (hb : d62854 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58497, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58497, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58498 q = 1) (hb : d62855 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58498, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58498, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2118 (p : Pattern) (ha : d58512 p = 1) (hb : d62858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h7 (q : Pattern) (ha : d58501 q = 1) (hb : d58656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58501, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58501, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58502 q = 1) (hb : d58657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58502, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58502, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58503 q = 1) (hb : d58658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58503, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58503, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4500 q = 1) (hb : d52857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro178 q ha hb
  have h11 (q : Pattern) (ha : d4501 q = 1) (hb : d58504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d58504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4501, d58504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4502 q = 1) (hb : d58505 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d58505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4502, d58505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4503 q = 1) (hb : d58506 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d58506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4503, d58506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58507 q = 1) (hb : d58659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58507, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58507, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58511 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58512 q = 1) (hb : d62858 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58512, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58512, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2119 (p : Pattern) (ha : d58518 p = 1) (hb : d62864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58513 q = 1) (hb : d62859 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58513, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58513, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2118 q ha hb
  have h2 (q : Pattern) (ha : d58514 q = 1) (hb : d62860 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58514, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58514, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58515 q = 1) (hb : d62861 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58515, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58515, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58516 q = 1) (hb : d62862 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58516, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58516, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58517 q = 1) (hb : d62863 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58517, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58517, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58518 q = 1) (hb : d62864 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58518, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58518, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2120 (p : Pattern) (ha : d58533 p = 1) (hb : d62868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h7 (q : Pattern) (ha : d58522 q = 1) (hb : d58670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58522, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58522, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58523 q = 1) (hb : d58671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58523, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58523, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58524 q = 1) (hb : d58672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58524, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58524, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4540 q = 1) (hb : d53172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro234 q ha hb
  have h11 (q : Pattern) (ha : d4541 q = 1) (hb : d58525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d58525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4541, d58525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4542 q = 1) (hb : d58526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d58526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4542, d58526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4543 q = 1) (hb : d58527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d58527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4543, d58527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58528 q = 1) (hb : d58673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58528, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58528, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58532 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58533 q = 1) (hb : d62868 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58533, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58533, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2121 (p : Pattern) (ha : d58539 p = 1) (hb : d62874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58534 q = 1) (hb : d62869 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58534, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58534, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2120 q ha hb
  have h2 (q : Pattern) (ha : d58535 q = 1) (hb : d62870 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58535, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58535, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58536 q = 1) (hb : d62871 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58536, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58536, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58537 q = 1) (hb : d62872 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58537, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58537, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58538 q = 1) (hb : d62873 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58538, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58538, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58539 q = 1) (hb : d62874 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58539, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58539, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2122 (p : Pattern) (ha : d58555 p = 1) (hb : d62879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h7 (q : Pattern) (ha : d58544 q = 1) (hb : d58685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58544, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d58544, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d58545 q = 1) (hb : d58686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58545, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58545, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d58546 q = 1) (hb : d58687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58546, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58546, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4581 q = 1) (hb : d53489 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro293 q ha hb
  have h11 (q : Pattern) (ha : d4582 q = 1) (hb : d58547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d58547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4582, d58547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4583 q = 1) (hb : d58548 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d58548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4583, d58548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4584 q = 1) (hb : d58549 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d58549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4584, d58549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d58550 q = 1) (hb : d58688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58550, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58550, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d58554 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d58555 q = 1) (hb : d62879 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58555, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58555, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro2123 (p : Pattern) (ha : d58561 p = 1) (hb : d62885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58556 q = 1) (hb : d62880 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58556, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58556, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2122 q ha hb
  have h2 (q : Pattern) (ha : d58557 q = 1) (hb : d62881 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58557, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58557, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58558 q = 1) (hb : d62882 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58558, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58558, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58559 q = 1) (hb : d62883 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58559, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58559, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58560 q = 1) (hb : d62884 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58560, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58560, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58561 q = 1) (hb : d62885 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58561, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58561, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2124 (p : Pattern) (ha : d58567 p = 1) (hb : d62891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d58480 q = 1) (hb : d62848 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58480, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2113 q ha hb
    | true =>
      simp only [d58480, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2115 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58499 q = 1) (hb : d62856 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58499, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58499, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2117 q ha hb
  have h3 (q : Pattern) (ha : d58500 q = 1) (hb : d62857 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58500, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58500, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58519 q = 1) (hb : d62865 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58519, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58519, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2119 q ha hb
  have h5 (q : Pattern) (ha : d58520 q = 1) (hb : d62866 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58520, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58520, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58521 q = 1) (hb : d62867 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58521, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58521, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58540 q = 1) (hb : d62875 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58540, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58540, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2121 q ha hb
  have h8 (q : Pattern) (ha : d58541 q = 1) (hb : d62876 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58541, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58541, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58542 q = 1) (hb : d62877 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58542, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58542, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58543 q = 1) (hb : d62878 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58543, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58543, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58562 q = 1) (hb : d62886 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58562, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58562, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2123 q ha hb
  have h12 (q : Pattern) (ha : d58563 q = 1) (hb : d62887 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58563, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58563, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58564 q = 1) (hb : d62888 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58564, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58564, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58565 q = 1) (hb : d62889 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58565, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58565, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58566 q = 1) (hb : d62890 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58566, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58566, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58567 q = 1) (hb : d62891 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58567, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58567, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2125 (p : Pattern) (ha : d58573 p = 1) (hb : d62897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58568 q = 1) (hb : d62892 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58568, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2124 q ha hb
    | true =>
      simp only [d58568, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58569 q = 1) (hb : d62893 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58569, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58569, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58570 q = 1) (hb : d62894 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58570, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58570, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58571 q = 1) (hb : d62895 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58571, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58571, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58572 q = 1) (hb : d62896 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58572, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58572, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58573 q = 1) (hb : d62897 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58573, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58573, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2126 (p : Pattern) (ha : d58579 p = 1) (hb : d62903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58574 q = 1) (hb : d62898 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58574, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2125 q ha hb
    | true =>
      simp only [d58574, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58575 q = 1) (hb : d62899 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58575, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58575, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58576 q = 1) (hb : d62900 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58576, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58576, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58577 q = 1) (hb : d62901 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58577, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58577, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58578 q = 1) (hb : d62902 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58578, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58578, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58579 q = 1) (hb : d62903 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58579, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58579, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2127 (p : Pattern) (ha : d58585 p = 1) (hb : d62909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58580 q = 1) (hb : d62904 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58580, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2126 q ha hb
    | true =>
      simp only [d58580, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58581 q = 1) (hb : d62905 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58581, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58581, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58582 q = 1) (hb : d62906 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58582, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58582, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58583 q = 1) (hb : d62907 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58583, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58583, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58584 q = 1) (hb : d62908 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58584, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58584, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58585 q = 1) (hb : d62909 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58585, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58585, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2128 (p : Pattern) (ha : d58591 p = 1) (hb : d62915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58586 q = 1) (hb : d62910 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58586, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2127 q ha hb
    | true =>
      simp only [d58586, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58587 q = 1) (hb : d62911 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58587, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58587, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58588 q = 1) (hb : d62912 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58588, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58588, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58589 q = 1) (hb : d62913 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58589, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58589, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58590 q = 1) (hb : d62914 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58590, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58590, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58591 q = 1) (hb : d62915 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58591, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58591, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2129 (p : Pattern) (ha : d58597 p = 1) (hb : d62921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58592 q = 1) (hb : d62916 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58592, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2128 q ha hb
    | true =>
      simp only [d58592, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58593 q = 1) (hb : d62917 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58593, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58593, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58594 q = 1) (hb : d62918 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58594, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58594, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58595 q = 1) (hb : d62919 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58595, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58595, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58596 q = 1) (hb : d62920 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58596, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58596, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58597 q = 1) (hb : d62921 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58597, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58597, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2130 (p : Pattern) (ha : d58603 p = 1) (hb : d62927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58598 q = 1) (hb : d62922 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58598, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2129 q ha hb
    | true =>
      simp only [d58598, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58599 q = 1) (hb : d62923 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58599, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58599, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58600 q = 1) (hb : d62924 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58600, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58600, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58601 q = 1) (hb : d62925 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58601, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58601, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58602 q = 1) (hb : d62926 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58602, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58602, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58603 q = 1) (hb : d62927 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58603, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58603, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2131 (p : Pattern) (ha : d58609 p = 1) (hb : d62933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58604 q = 1) (hb : d62928 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58604, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2130 q ha hb
    | true =>
      simp only [d58604, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58605 q = 1) (hb : d62929 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58605, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58605, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58606 q = 1) (hb : d62930 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58606, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58606, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58607 q = 1) (hb : d62931 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58607, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58607, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58608 q = 1) (hb : d62932 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58608, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58608, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58609 q = 1) (hb : d62933 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58609, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58609, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2132 (p : Pattern) (ha : d54509 p = 1) (hb : d62827 p = 1) : d54509 p = 1 := by
  have h0 (q : Pattern) (ha : d54509 q = 1) (hb : d62827 q = 1) : d54509 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2133 (p : Pattern) (ha : d54404 p = 1) (hb : d58438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d112, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro324 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d58434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d58434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d58434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53637 q = 1) (hb : d58435 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d58435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d58435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53638 q = 1) (hb : d58436 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d58436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d58436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d407 q = 1) (hb : d52039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d407, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro325 q ha hb
  have h7 (q : Pattern) (ha : d52040 q = 1) (hb : d53639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52040, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d52041 q = 1) (hb : d53640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52041, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d52042 q = 1) (hb : d53641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52042, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d53642 q = 1) (hb : d58437 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d58437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53642, d58437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54404 q = 1) (hb : d58438 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d58438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54404, d58438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2134 (p : Pattern) (ha : d54410 p = 1) (hb : d58455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d292, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro329 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d58444 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d58444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d58444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53653 q = 1) (hb : d58445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d58445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d58445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53654 q = 1) (hb : d58446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d58446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d58446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52171 q = 1) (hb : d53656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52171, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52171, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro330 q ha hb
  have h7 (q : Pattern) (ha : d53657 q = 1) (hb : d58447 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d58447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53657, d58447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53658 q = 1) (hb : d58448 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d58448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53658, d58448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53659 q = 1) (hb : d58449 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d58449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53659, d58449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53660 q = 1) (hb : d58450 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d58450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53660, d58450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58454 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54410 q = 1) (hb : d58455 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d58455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54410, d58455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2135 (p : Pattern) (ha : d54416 p = 1) (hb : d58461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54405 q = 1) (hb : d58439 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d58439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54405, d58439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2133 q ha hb
  have h3 (q : Pattern) (ha : d54406 q = 1) (hb : d58440 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d58440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54406, d58440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54407 q = 1) (hb : d58441 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d58441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54407, d58441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54408 q = 1) (hb : d58442 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d58442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54408, d58442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54409 q = 1) (hb : d58443 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d58443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d58443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54411 q = 1) (hb : d58456 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d58456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54411, d58456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2134 q ha hb
  have h8 (q : Pattern) (ha : d54412 q = 1) (hb : d58457 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d58457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54412, d58457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54413 q = 1) (hb : d58458 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d58458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54413, d58458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54414 q = 1) (hb : d58459 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d58459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54414, d58459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54415 q = 1) (hb : d58460 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d58460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54415, d58460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54416 q = 1) (hb : d58461 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d58461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54416, d58461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2136 (p : Pattern) (ha : d54417 p = 1) (hb : d58473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d508, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d58462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d58462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d58462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53678 q = 1) (hb : d58463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d58463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d58463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53679 q = 1) (hb : d58464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d58464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d58464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52356 q = 1) (hb : d53681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52356, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52356, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro336 q ha hb
  have h7 (q : Pattern) (ha : d53682 q = 1) (hb : d58465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d58465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53682, d58465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53683 q = 1) (hb : d58466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d58466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53683, d58466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53684 q = 1) (hb : d58467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d58467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53684, d58467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53685 q = 1) (hb : d58468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d58468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53685, d58468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58472 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54417 q = 1) (hb : d58473 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d58473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54417, d58473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2137 (p : Pattern) (ha : d54423 p = 1) (hb : d58479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d58474 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d58474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d58474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2136 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d58475 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d58475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d58475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d58476 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d58476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d58476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d58477 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d58477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d58477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d58478 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d58478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d58478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d58479 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d58479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d58479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2138 (p : Pattern) (ha : d54425 p = 1) (hb : d58492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d800, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d58481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d58481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d58481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53705 q = 1) (hb : d58482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d58482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d58482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53706 q = 1) (hb : d58483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d58483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d58483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52577 q = 1) (hb : d53708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52577, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52577, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro342 q ha hb
  have h7 (q : Pattern) (ha : d53709 q = 1) (hb : d58484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d58484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53709, d58484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53710 q = 1) (hb : d58485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d58485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53710, d58485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53711 q = 1) (hb : d58486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d58486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53711, d58486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53712 q = 1) (hb : d58487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d58487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53712, d58487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58491 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54425 q = 1) (hb : d58492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d58492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54425, d58492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2139 (p : Pattern) (ha : d54431 p = 1) (hb : d58498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d58493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d58493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d58493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2138 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d58494 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d58494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d58494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d58495 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d58495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d58495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d58496 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d58496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d58496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d58497 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d58497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d58497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d58498 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d58498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d58498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2140 (p : Pattern) (ha : d54434 p = 1) (hb : d58512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d1179, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro347 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d58501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d58501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d58501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53733 q = 1) (hb : d58502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d58502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d58502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53734 q = 1) (hb : d58503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d58503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d58503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52857 q = 1) (hb : d53736 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52857, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52857, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro348 q ha hb
  have h7 (q : Pattern) (ha : d53737 q = 1) (hb : d58504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d58504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53737, d58504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53738 q = 1) (hb : d58505 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d58505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53738, d58505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53739 q = 1) (hb : d58506 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d58506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53739, d58506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53740 q = 1) (hb : d58507 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d58507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53740, d58507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58511 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54434 q = 1) (hb : d58512 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54434, d58512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54434, d58512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2141 (p : Pattern) (ha : d54440 p = 1) (hb : d58518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54435 q = 1) (hb : d58513 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54435, d58513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54435, d58513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2140 q ha hb
  have h2 (q : Pattern) (ha : d54436 q = 1) (hb : d58514 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54436, d58514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54436, d58514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54437 q = 1) (hb : d58515 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54437, d58515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54437, d58515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54438 q = 1) (hb : d58516 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54438, d58516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54438, d58516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54439 q = 1) (hb : d58517 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54439, d58517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54439, d58517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54440 q = 1) (hb : d58518 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54440, d58518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54440, d58518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2142 (p : Pattern) (ha : d54444 p = 1) (hb : d58533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d1640, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro353 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d58522 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d58522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d58522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53762 q = 1) (hb : d58523 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d58523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d58523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53763 q = 1) (hb : d58524 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d58524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d58524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53172 q = 1) (hb : d53765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53172, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53172, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro354 q ha hb
  have h7 (q : Pattern) (ha : d53766 q = 1) (hb : d58525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d58525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53766, d58525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53767 q = 1) (hb : d58526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d58526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53767, d58526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53768 q = 1) (hb : d58527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d58527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53768, d58527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53769 q = 1) (hb : d58528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d58528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53769, d58528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58532 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54444 q = 1) (hb : d58533 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54444, d58533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54444, d58533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2143 (p : Pattern) (ha : d54450 p = 1) (hb : d58539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54445 q = 1) (hb : d58534 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54445, d58534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54445, d58534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2142 q ha hb
  have h2 (q : Pattern) (ha : d54446 q = 1) (hb : d58535 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54446, d58535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54446, d58535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54447 q = 1) (hb : d58536 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54447, d58536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54447, d58536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54448 q = 1) (hb : d58537 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54448, d58537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54448, d58537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54449 q = 1) (hb : d58538 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54449, d58538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54449, d58538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54450 q = 1) (hb : d58539 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54450, d58539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54450, d58539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2144 (p : Pattern) (ha : d54455 p = 1) (hb : d58555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d2123, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d58544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d58544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d58544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53792 q = 1) (hb : d58545 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d58545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d58545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53793 q = 1) (hb : d58546 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d58546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d58546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53489 q = 1) (hb : d53795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53489, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53489, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro360 q ha hb
  have h7 (q : Pattern) (ha : d53796 q = 1) (hb : d58547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d58547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53796, d58547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53797 q = 1) (hb : d58548 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d58548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53797, d58548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53798 q = 1) (hb : d58549 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d58549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53798, d58549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53799 q = 1) (hb : d58550 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d58550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53799, d58550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58554 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54455 q = 1) (hb : d58555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54455, d58555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54455, d58555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2145 (p : Pattern) (ha : d54461 p = 1) (hb : d58561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54456 q = 1) (hb : d58556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54456, d58556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54456, d58556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2144 q ha hb
  have h2 (q : Pattern) (ha : d54457 q = 1) (hb : d58557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54457, d58557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54457, d58557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54458 q = 1) (hb : d58558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54458, d58558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54458, d58558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54459 q = 1) (hb : d58559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54459, d58559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54459, d58559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54460 q = 1) (hb : d58560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54460, d58560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54460, d58560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54461 q = 1) (hb : d58561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54461, d58561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54461, d58561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2146 (p : Pattern) (ha : d54467 p = 1) (hb : d58567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54424 q = 1) (hb : d58480 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54424, d58480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2135 q ha hb
    | true =>
      simp only [d54424, d58480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2137 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54432 q = 1) (hb : d58499 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54432, d58499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54432, d58499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2139 q ha hb
  have h3 (q : Pattern) (ha : d54433 q = 1) (hb : d58500 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54433, d58500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54433, d58500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54441 q = 1) (hb : d58519 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54441, d58519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54441, d58519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2141 q ha hb
  have h5 (q : Pattern) (ha : d54442 q = 1) (hb : d58520 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54442, d58520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54442, d58520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54443 q = 1) (hb : d58521 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54443, d58521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54443, d58521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54451 q = 1) (hb : d58540 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54451, d58540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54451, d58540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2143 q ha hb
  have h8 (q : Pattern) (ha : d54452 q = 1) (hb : d58541 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54452, d58541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54452, d58541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54453 q = 1) (hb : d58542 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54453, d58542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54453, d58542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54454 q = 1) (hb : d58543 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54454, d58543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54454, d58543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54462 q = 1) (hb : d58562 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54462, d58562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54462, d58562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2145 q ha hb
  have h12 (q : Pattern) (ha : d54463 q = 1) (hb : d58563 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54463, d58563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54463, d58563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54464 q = 1) (hb : d58564 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54464, d58564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54464, d58564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54465 q = 1) (hb : d58565 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54465, d58565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54465, d58565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54466 q = 1) (hb : d58566 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54466, d58566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54466, d58566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54467 q = 1) (hb : d58567 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54467, d58567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54467, d58567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2147 (p : Pattern) (ha : d54473 p = 1) (hb : d58573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54468 q = 1) (hb : d58568 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54468, d58568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2146 q ha hb
    | true =>
      simp only [d54468, d58568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54469 q = 1) (hb : d58569 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54469, d58569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54469, d58569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54470 q = 1) (hb : d58570 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54470, d58570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54470, d58570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54471 q = 1) (hb : d58571 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54471, d58571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54471, d58571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54472 q = 1) (hb : d58572 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54472, d58572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54472, d58572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54473 q = 1) (hb : d58573 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54473, d58573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54473, d58573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2148 (p : Pattern) (ha : d54479 p = 1) (hb : d58579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54474 q = 1) (hb : d58574 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54474, d58574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2147 q ha hb
    | true =>
      simp only [d54474, d58574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54475 q = 1) (hb : d58575 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54475, d58575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54475, d58575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54476 q = 1) (hb : d58576 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54476, d58576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54476, d58576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54477 q = 1) (hb : d58577 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54477, d58577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54477, d58577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54478 q = 1) (hb : d58578 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54478, d58578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54478, d58578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54479 q = 1) (hb : d58579 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54479, d58579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54479, d58579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2149 (p : Pattern) (ha : d54485 p = 1) (hb : d58585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54480 q = 1) (hb : d58580 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54480, d58580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2148 q ha hb
    | true =>
      simp only [d54480, d58580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54481 q = 1) (hb : d58581 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54481, d58581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54481, d58581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54482 q = 1) (hb : d58582 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54482, d58582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54482, d58582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54483 q = 1) (hb : d58583 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54483, d58583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54483, d58583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54484 q = 1) (hb : d58584 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54484, d58584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54484, d58584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54485 q = 1) (hb : d58585 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54485, d58585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54485, d58585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2150 (p : Pattern) (ha : d54491 p = 1) (hb : d58591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54486 q = 1) (hb : d58586 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54486, d58586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2149 q ha hb
    | true =>
      simp only [d54486, d58586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54487 q = 1) (hb : d58587 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54487, d58587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54487, d58587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54488 q = 1) (hb : d58588 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54488, d58588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54488, d58588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54489 q = 1) (hb : d58589 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54489, d58589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54489, d58589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54490 q = 1) (hb : d58590 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54490, d58590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54490, d58590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54491 q = 1) (hb : d58591 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54491, d58591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54491, d58591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2151 (p : Pattern) (ha : d54497 p = 1) (hb : d58597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54492 q = 1) (hb : d58592 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54492, d58592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2150 q ha hb
    | true =>
      simp only [d54492, d58592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54493 q = 1) (hb : d58593 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54493, d58593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54493, d58593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54494 q = 1) (hb : d58594 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54494, d58594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54494, d58594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54495 q = 1) (hb : d58595 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54495, d58595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54495, d58595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54496 q = 1) (hb : d58596 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54496, d58596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54496, d58596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54497 q = 1) (hb : d58597 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54497, d58597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54497, d58597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2152 (p : Pattern) (ha : d54503 p = 1) (hb : d58603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54498 q = 1) (hb : d58598 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54498, d58598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2151 q ha hb
    | true =>
      simp only [d54498, d58598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54499 q = 1) (hb : d58599 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54499, d58599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54499, d58599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54500 q = 1) (hb : d58600 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54500, d58600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54500, d58600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54501 q = 1) (hb : d58601 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54501, d58601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54501, d58601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54502 q = 1) (hb : d58602 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54502, d58602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54502, d58602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54503 q = 1) (hb : d58603 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54503, d58603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54503, d58603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2153 (p : Pattern) (ha : d54509 p = 1) (hb : d58609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54504 q = 1) (hb : d58604 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54504, d58604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2152 q ha hb
    | true =>
      simp only [d54504, d58604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54505 q = 1) (hb : d58605 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54505, d58605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54505, d58605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54506 q = 1) (hb : d58606 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54506, d58606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54506, d58606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54507 q = 1) (hb : d58607 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54507, d58607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54507, d58607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54508 q = 1) (hb : d58608 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54508, d58608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54508, d58608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54509 q = 1) (hb : d58609 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54509, d58609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54509, d58609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2154 (p : Pattern) (ha : d54404 p = 1) (hb : d58614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d112, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d58610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53637 q = 1) (hb : d58611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53638 q = 1) (hb : d58612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d407 q = 1) (hb : d4350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d407, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro374 q ha hb
  have h7 (q : Pattern) (ha : d4351 q = 1) (hb : d53639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d4351, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4352 q = 1) (hb : d53640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4352, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4353 q = 1) (hb : d53641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4353, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53642 q = 1) (hb : d58613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53642, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4364 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54404 q = 1) (hb : d58614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54404, d58614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54404, d58614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2155 (p : Pattern) (ha : d54410 p = 1) (hb : d58624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d292, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro378 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d58620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53653 q = 1) (hb : d58621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53654 q = 1) (hb : d58622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4386 q = 1) (hb : d53656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4386, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro379 q ha hb
  have h7 (q : Pattern) (ha : d4387 q = 1) (hb : d53657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4387, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4388 q = 1) (hb : d53658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4388, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4389 q = 1) (hb : d53659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4389, d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53660 q = 1) (hb : d58623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53660, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4400 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54410 q = 1) (hb : d58624 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54410, d58624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54410, d58624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2156 (p : Pattern) (ha : d54416 p = 1) (hb : d58630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54405 q = 1) (hb : d58615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54405, d58615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54405, d58615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2154 q ha hb
  have h3 (q : Pattern) (ha : d54406 q = 1) (hb : d58616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54406, d58616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54406, d58616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54407 q = 1) (hb : d58617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54407, d58617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54407, d58617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54408 q = 1) (hb : d58618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54408, d58618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54408, d58618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54409 q = 1) (hb : d58619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54409, d58619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54409, d58619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54411 q = 1) (hb : d58625 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54411, d58625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54411, d58625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2155 q ha hb
  have h8 (q : Pattern) (ha : d54412 q = 1) (hb : d58626 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54412, d58626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54412, d58626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54413 q = 1) (hb : d58627 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54413, d58627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54413, d58627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54414 q = 1) (hb : d58628 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54414, d58628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54414, d58628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54415 q = 1) (hb : d58629 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54415, d58629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54415, d58629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54416 q = 1) (hb : d58630 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54416, d58630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54416, d58630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2157 (p : Pattern) (ha : d54417 p = 1) (hb : d58635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d508, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro384 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d58631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53678 q = 1) (hb : d58632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53679 q = 1) (hb : d58633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4423 q = 1) (hb : d53681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4423, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro385 q ha hb
  have h7 (q : Pattern) (ha : d4424 q = 1) (hb : d53682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4424, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4425 q = 1) (hb : d53683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4425, d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4426 q = 1) (hb : d53684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4426, d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53685 q = 1) (hb : d58634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53685, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4437 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54417 q = 1) (hb : d58635 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54417, d58635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54417, d58635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2158 (p : Pattern) (ha : d54423 p = 1) (hb : d58641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54418 q = 1) (hb : d58636 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54418, d58636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54418, d58636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2157 q ha hb
  have h2 (q : Pattern) (ha : d54419 q = 1) (hb : d58637 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54419, d58637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54419, d58637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54420 q = 1) (hb : d58638 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54420, d58638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54420, d58638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54421 q = 1) (hb : d58639 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54421, d58639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54421, d58639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54422 q = 1) (hb : d58640 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54422, d58640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54422, d58640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54423 q = 1) (hb : d58641 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54423, d58641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54423, d58641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2159 (p : Pattern) (ha : d54425 p = 1) (hb : d58647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d800, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro390 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d58643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53705 q = 1) (hb : d58644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53706 q = 1) (hb : d58645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4461 q = 1) (hb : d53708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4461, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro391 q ha hb
  have h7 (q : Pattern) (ha : d4462 q = 1) (hb : d53709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4462, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4463 q = 1) (hb : d53710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4463, d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4464 q = 1) (hb : d53711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4464, d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53712 q = 1) (hb : d58646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53712, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4475 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54425 q = 1) (hb : d58647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54425, d58647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54425, d58647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2160 (p : Pattern) (ha : d54431 p = 1) (hb : d58653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54426 q = 1) (hb : d58648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54426, d58648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54426, d58648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2159 q ha hb
  have h2 (q : Pattern) (ha : d54427 q = 1) (hb : d58649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54427, d58649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54427, d58649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54428 q = 1) (hb : d58650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54428, d58650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54428, d58650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54429 q = 1) (hb : d58651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54429, d58651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54429, d58651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54430 q = 1) (hb : d58652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54430, d58652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54430, d58652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54431 q = 1) (hb : d58653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54431, d58653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54431, d58653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2161 (p : Pattern) (ha : d54434 p = 1) (hb : d58660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d1179, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d58656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53733 q = 1) (hb : d58657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53734 q = 1) (hb : d58658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4500 q = 1) (hb : d53736 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4500, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro397 q ha hb
  have h7 (q : Pattern) (ha : d4501 q = 1) (hb : d53737 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4501, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4502 q = 1) (hb : d53738 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4502, d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4503 q = 1) (hb : d53739 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4503, d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53740 q = 1) (hb : d58659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53740, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4514 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54434 q = 1) (hb : d58660 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54434, d58660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54434, d58660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2162 (p : Pattern) (ha : d54440 p = 1) (hb : d58666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54435 q = 1) (hb : d58661 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54435, d58661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54435, d58661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2161 q ha hb
  have h2 (q : Pattern) (ha : d54436 q = 1) (hb : d58662 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54436, d58662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54436, d58662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54437 q = 1) (hb : d58663 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54437, d58663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54437, d58663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54438 q = 1) (hb : d58664 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54438, d58664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54438, d58664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54439 q = 1) (hb : d58665 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54439, d58665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54439, d58665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54440 q = 1) (hb : d58666 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54440, d58666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54440, d58666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2163 (p : Pattern) (ha : d54444 p = 1) (hb : d58674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d1640, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d58670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53762 q = 1) (hb : d58671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53763 q = 1) (hb : d58672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4540 q = 1) (hb : d53765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4540, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro403 q ha hb
  have h7 (q : Pattern) (ha : d4541 q = 1) (hb : d53766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4541, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4542 q = 1) (hb : d53767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4542, d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4543 q = 1) (hb : d53768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4543, d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53769 q = 1) (hb : d58673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53769, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4554 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54444 q = 1) (hb : d58674 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54444, d58674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54444, d58674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2164 (p : Pattern) (ha : d54450 p = 1) (hb : d58680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54445 q = 1) (hb : d58675 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54445, d58675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54445, d58675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2163 q ha hb
  have h2 (q : Pattern) (ha : d54446 q = 1) (hb : d58676 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54446, d58676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54446, d58676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54447 q = 1) (hb : d58677 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54447, d58677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54447, d58677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54448 q = 1) (hb : d58678 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54448, d58678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54448, d58678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54449 q = 1) (hb : d58679 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54449, d58679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54449, d58679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54450 q = 1) (hb : d58680 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54450, d58680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54450, d58680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2165 (p : Pattern) (ha : d54455 p = 1) (hb : d58689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d2123, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d58685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53792 q = 1) (hb : d58686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53793 q = 1) (hb : d58687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4581 q = 1) (hb : d53795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4581, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro409 q ha hb
  have h7 (q : Pattern) (ha : d4582 q = 1) (hb : d53796 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4582, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d4583 q = 1) (hb : d53797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4583, d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4584 q = 1) (hb : d53798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4584, d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d53799 q = 1) (hb : d58688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53799, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d4595 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54455 q = 1) (hb : d58689 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54455, d58689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54455, d58689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2166 (p : Pattern) (ha : d54461 p = 1) (hb : d58695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54456 q = 1) (hb : d58690 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54456, d58690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54456, d58690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2165 q ha hb
  have h2 (q : Pattern) (ha : d54457 q = 1) (hb : d58691 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54457, d58691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54457, d58691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54458 q = 1) (hb : d58692 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54458, d58692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54458, d58692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54459 q = 1) (hb : d58693 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54459, d58693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54459, d58693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54460 q = 1) (hb : d58694 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54460, d58694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54460, d58694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54461 q = 1) (hb : d58695 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54461, d58695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54461, d58695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2167 (p : Pattern) (ha : d54467 p = 1) (hb : d58701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54424 q = 1) (hb : d58642 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54424, d58642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2156 q ha hb
    | true =>
      simp only [d54424, d58642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2158 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54432 q = 1) (hb : d58654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54432, d58654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54432, d58654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2160 q ha hb
  have h3 (q : Pattern) (ha : d54433 q = 1) (hb : d58655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54433, d58655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54433, d58655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54441 q = 1) (hb : d58667 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54441, d58667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54441, d58667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2162 q ha hb
  have h5 (q : Pattern) (ha : d54442 q = 1) (hb : d58668 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54442, d58668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54442, d58668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54443 q = 1) (hb : d58669 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54443, d58669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54443, d58669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54451 q = 1) (hb : d58681 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54451, d58681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54451, d58681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2164 q ha hb
  have h8 (q : Pattern) (ha : d54452 q = 1) (hb : d58682 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54452, d58682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54452, d58682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54453 q = 1) (hb : d58683 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54453, d58683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54453, d58683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54454 q = 1) (hb : d58684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54454, d58684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54454, d58684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54462 q = 1) (hb : d58696 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54462, d58696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54462, d58696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2166 q ha hb
  have h12 (q : Pattern) (ha : d54463 q = 1) (hb : d58697 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54463, d58697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54463, d58697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54464 q = 1) (hb : d58698 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54464, d58698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54464, d58698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54465 q = 1) (hb : d58699 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54465, d58699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54465, d58699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54466 q = 1) (hb : d58700 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54466, d58700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54466, d58700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54467 q = 1) (hb : d58701 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54467, d58701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54467, d58701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2168 (p : Pattern) (ha : d54473 p = 1) (hb : d58707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54468 q = 1) (hb : d58702 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54468, d58702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2167 q ha hb
    | true =>
      simp only [d54468, d58702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54469 q = 1) (hb : d58703 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54469, d58703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54469, d58703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54470 q = 1) (hb : d58704 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54470, d58704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54470, d58704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54471 q = 1) (hb : d58705 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54471, d58705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54471, d58705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54472 q = 1) (hb : d58706 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54472, d58706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54472, d58706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54473 q = 1) (hb : d58707 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54473, d58707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54473, d58707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2169 (p : Pattern) (ha : d54479 p = 1) (hb : d58713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54474 q = 1) (hb : d58708 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54474, d58708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2168 q ha hb
    | true =>
      simp only [d54474, d58708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54475 q = 1) (hb : d58709 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54475, d58709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54475, d58709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54476 q = 1) (hb : d58710 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54476, d58710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54476, d58710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54477 q = 1) (hb : d58711 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54477, d58711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54477, d58711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54478 q = 1) (hb : d58712 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54478, d58712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54478, d58712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54479 q = 1) (hb : d58713 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54479, d58713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54479, d58713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2170 (p : Pattern) (ha : d54485 p = 1) (hb : d58719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54480 q = 1) (hb : d58714 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54480, d58714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2169 q ha hb
    | true =>
      simp only [d54480, d58714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54481 q = 1) (hb : d58715 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54481, d58715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54481, d58715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54482 q = 1) (hb : d58716 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54482, d58716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54482, d58716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54483 q = 1) (hb : d58717 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54483, d58717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54483, d58717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54484 q = 1) (hb : d58718 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54484, d58718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54484, d58718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54485 q = 1) (hb : d58719 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54485, d58719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54485, d58719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2171 (p : Pattern) (ha : d54491 p = 1) (hb : d58725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54486 q = 1) (hb : d58720 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54486, d58720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2170 q ha hb
    | true =>
      simp only [d54486, d58720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54487 q = 1) (hb : d58721 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54487, d58721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54487, d58721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54488 q = 1) (hb : d58722 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54488, d58722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54488, d58722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54489 q = 1) (hb : d58723 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54489, d58723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54489, d58723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54490 q = 1) (hb : d58724 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54490, d58724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54490, d58724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54491 q = 1) (hb : d58725 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54491, d58725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54491, d58725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2172 (p : Pattern) (ha : d54497 p = 1) (hb : d58731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54492 q = 1) (hb : d58726 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54492, d58726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2171 q ha hb
    | true =>
      simp only [d54492, d58726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54493 q = 1) (hb : d58727 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54493, d58727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54493, d58727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54494 q = 1) (hb : d58728 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54494, d58728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54494, d58728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54495 q = 1) (hb : d58729 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54495, d58729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54495, d58729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54496 q = 1) (hb : d58730 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54496, d58730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54496, d58730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54497 q = 1) (hb : d58731 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54497, d58731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54497, d58731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2173 (p : Pattern) (ha : d54503 p = 1) (hb : d58737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54498 q = 1) (hb : d58732 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54498, d58732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2172 q ha hb
    | true =>
      simp only [d54498, d58732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54499 q = 1) (hb : d58733 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54499, d58733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54499, d58733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54500 q = 1) (hb : d58734 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54500, d58734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54500, d58734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54501 q = 1) (hb : d58735 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54501, d58735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54501, d58735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54502 q = 1) (hb : d58736 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54502, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54502, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54503 q = 1) (hb : d58737 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54503, d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54503, d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2174 (p : Pattern) (ha : d54509 p = 1) (hb : d58743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54504 q = 1) (hb : d58738 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54504, d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2173 q ha hb
    | true =>
      simp only [d54504, d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54505 q = 1) (hb : d58739 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54505, d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54505, d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54506 q = 1) (hb : d58740 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54506, d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54506, d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54507 q = 1) (hb : d58741 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54507, d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54507, d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54508 q = 1) (hb : d58742 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54508, d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54508, d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54509 q = 1) (hb : d58743 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54509, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54509, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2175 (p : Pattern) (ha : d54518 p = 1) (hb : d54863 p = 1) : d54863 p = 1 := by
  have h0 (q : Pattern) (ha : d54518 q = 1) (hb : d54863 q = 1) : d54863 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro2176 (p : Pattern) (ha : d2520 p = 1) (hb : d62934 p = 1) : d3503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d54978 q = 1) : d3498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1915 q ha hb
    | true =>
      simp only [d56, d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1916 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d54978 q = 1) : d3499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d54978 q = 1) : d3500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d54978 q = 1) : d3501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2519 q = 1) (hb : d62934 q = 1) : d3502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, d62934, d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2519, d62934, d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2520 q = 1) (hb : d62934 q = 1) : d3503 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2520, d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2177 (p : Pattern) (ha : d54752 p = 1) (hb : d62934 p = 1) : d62560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d54978 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d54978 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d54978 q = 1) : d3508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d54978 q = 1) : d62555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1920 q ha hb
    | true =>
      simp only [d51647, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1921 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d54978 q = 1) : d214 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d54978 q = 1) : d62556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d54978 q = 1) : d62557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d54978 q = 1) : d62558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54751 q = 1) (hb : d62934 q = 1) : d62559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54751, d62934, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54751, d62934, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54752 q = 1) (hb : d62934 q = 1) : d62560 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54752, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54752, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2178 (p : Pattern) (ha : d54759 p = 1) (hb : d62934 p = 1) : d62572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d54978 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d54978 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d54978 q = 1) : d3521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d54978 q = 1) : d62567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1926 q ha hb
    | true =>
      simp only [d51664, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1927 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d54978 q = 1) : d3524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1925 q ha hb
    | true =>
      simp only [d398, d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d54978 q = 1) : d62568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d54978 q = 1) : d62569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d54978 q = 1) : d62570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54758 q = 1) (hb : d62934 q = 1) : d62571 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54758, d62934, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54758, d62934, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54759 q = 1) (hb : d62934 q = 1) : d62572 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54759, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54759, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2179 (p : Pattern) (ha : d54765 p = 1) (hb : d62934 p = 1) : d62578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d62934 q = 1) : d3504 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2176 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d62934 q = 1) : d3505 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d62934 q = 1) : d3506 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d62934 q = 1) : d3507 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54753 q = 1) (hb : d62934 q = 1) : d62561 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54753, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54753, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2177 q ha hb
  have h6 (q : Pattern) (ha : d54754 q = 1) (hb : d62934 q = 1) : d62562 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54754, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54754, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54755 q = 1) (hb : d62934 q = 1) : d62563 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54755, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54755, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54756 q = 1) (hb : d62934 q = 1) : d62564 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54756, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54756, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54757 q = 1) (hb : d62934 q = 1) : d62565 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54757, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54757, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54760 q = 1) (hb : d62934 q = 1) : d62573 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54760, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54760, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2178 q ha hb
  have h11 (q : Pattern) (ha : d54761 q = 1) (hb : d62934 q = 1) : d62574 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54761, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54761, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54762 q = 1) (hb : d62934 q = 1) : d62575 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54762, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54762, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54763 q = 1) (hb : d62934 q = 1) : d62576 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54763, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54763, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54764 q = 1) (hb : d62934 q = 1) : d62577 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54764, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54764, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54765 q = 1) (hb : d62934 q = 1) : d62578 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54765, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54765, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2180 (p : Pattern) (ha : d54767 p = 1) (hb : d62934 p = 1) : d62585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d54978 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d54978 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d54978 q = 1) : d3536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d54978 q = 1) : d62580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1934 q ha hb
    | true =>
      simp only [d51689, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1935 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d54978 q = 1) : d3540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1932 q ha hb
    | true =>
      simp only [d645, d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1933 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d54978 q = 1) : d62581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d54978 q = 1) : d62582 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d54978 q = 1) : d62583 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54766 q = 1) (hb : d62934 q = 1) : d62584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54766, d62934, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54766, d62934, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54767 q = 1) (hb : d62934 q = 1) : d62585 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54767, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54767, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2181 (p : Pattern) (ha : d54773 p = 1) (hb : d62934 p = 1) : d62591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54768 q = 1) (hb : d62934 q = 1) : d62586 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54768, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54768, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2180 q ha hb
  have h2 (q : Pattern) (ha : d54769 q = 1) (hb : d62934 q = 1) : d62587 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54769, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54769, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54770 q = 1) (hb : d62934 q = 1) : d62588 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54770, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54770, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54771 q = 1) (hb : d62934 q = 1) : d62589 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54771, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54771, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54772 q = 1) (hb : d62934 q = 1) : d62590 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54772, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54772, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54773 q = 1) (hb : d62934 q = 1) : d62591 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54773, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54773, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2182 (p : Pattern) (ha : d54776 p = 1) (hb : d62934 p = 1) : d62599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d54978 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d54978 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d54978 q = 1) : d3553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d54978 q = 1) : d62594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1942 q ha hb
    | true =>
      simp only [d51715, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1943 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d54978 q = 1) : d3557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1940 q ha hb
    | true =>
      simp only [d951, d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1941 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d54978 q = 1) : d62595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d54978 q = 1) : d62596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d54978 q = 1) : d62597 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54775 q = 1) (hb : d62934 q = 1) : d62598 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54775, d62934, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54775, d62934, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54776 q = 1) (hb : d62934 q = 1) : d62599 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54776, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54776, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2183 (p : Pattern) (ha : d54782 p = 1) (hb : d62934 p = 1) : d62605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54777 q = 1) (hb : d62934 q = 1) : d62600 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54777, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54777, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2182 q ha hb
  have h2 (q : Pattern) (ha : d54778 q = 1) (hb : d62934 q = 1) : d62601 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54778, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54778, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54779 q = 1) (hb : d62934 q = 1) : d62602 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54779, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54779, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54780 q = 1) (hb : d62934 q = 1) : d62603 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54780, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54780, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54781 q = 1) (hb : d62934 q = 1) : d62604 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54781, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54781, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54782 q = 1) (hb : d62934 q = 1) : d62605 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54782, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54782, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2184 (p : Pattern) (ha : d54786 p = 1) (hb : d62934 p = 1) : d62614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d54978 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d54978 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d54978 q = 1) : d3571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d54978 q = 1) : d62609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1950 q ha hb
    | true =>
      simp only [d51742, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1951 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d54978 q = 1) : d3575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1948 q ha hb
    | true =>
      simp only [d1362, d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1949 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d54978 q = 1) : d62610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d54978 q = 1) : d62611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d54978 q = 1) : d62612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54785 q = 1) (hb : d62934 q = 1) : d62613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54785, d62934, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54785, d62934, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54786 q = 1) (hb : d62934 q = 1) : d62614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54786, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54786, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2185 (p : Pattern) (ha : d54792 p = 1) (hb : d62934 p = 1) : d62620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54787 q = 1) (hb : d62934 q = 1) : d62615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54787, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54787, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2184 q ha hb
  have h2 (q : Pattern) (ha : d54788 q = 1) (hb : d62934 q = 1) : d62616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54788, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54788, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54789 q = 1) (hb : d62934 q = 1) : d62617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54789, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54789, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54790 q = 1) (hb : d62934 q = 1) : d62618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54790, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54790, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54791 q = 1) (hb : d62934 q = 1) : d62619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54791, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54791, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54792 q = 1) (hb : d62934 q = 1) : d62620 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54792, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54792, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2186 (p : Pattern) (ha : d54797 p = 1) (hb : d62934 p = 1) : d62630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d54978 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d54978 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d54978 q = 1) : d3590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d54978 q = 1) : d62625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1958 q ha hb
    | true =>
      simp only [d51770, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1959 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d54978 q = 1) : d3594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1956 q ha hb
    | true =>
      simp only [d1839, d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1957 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d54978 q = 1) : d62626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d54978 q = 1) : d62627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d54978 q = 1) : d62628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54796 q = 1) (hb : d62934 q = 1) : d62629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54796, d62934, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54796, d62934, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54797 q = 1) (hb : d62934 q = 1) : d62630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54797, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54797, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2187 (p : Pattern) (ha : d54803 p = 1) (hb : d62934 p = 1) : d62636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54798 q = 1) (hb : d62934 q = 1) : d62631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54798, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54798, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2186 q ha hb
  have h2 (q : Pattern) (ha : d54799 q = 1) (hb : d62934 q = 1) : d62632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54799, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54799, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54800 q = 1) (hb : d62934 q = 1) : d62633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54800, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54800, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54801 q = 1) (hb : d62934 q = 1) : d62634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54801, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54801, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54802 q = 1) (hb : d62934 q = 1) : d62635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54802, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54802, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54803 q = 1) (hb : d62934 q = 1) : d62636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54803, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54803, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2188 (p : Pattern) (ha : d54809 p = 1) (hb : d62934 p = 1) : d62647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d54978 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d54978 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d54978 q = 1) : d3610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d54978 q = 1) : d62642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1966 q ha hb
    | true =>
      simp only [d51799, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1967 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d54978 q = 1) : d3614 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1964 q ha hb
    | true =>
      simp only [d2317, d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1965 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d54978 q = 1) : d62643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d54978 q = 1) : d62644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d54978 q = 1) : d62645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54808 q = 1) (hb : d62934 q = 1) : d62646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54808, d62934, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54808, d62934, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54809 q = 1) (hb : d62934 q = 1) : d62647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54809, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54809, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2189 (p : Pattern) (ha : d54815 p = 1) (hb : d62934 p = 1) : d62653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54810 q = 1) (hb : d62934 q = 1) : d62648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54810, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54810, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2188 q ha hb
  have h2 (q : Pattern) (ha : d54811 q = 1) (hb : d62934 q = 1) : d62649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54811, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54811, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54812 q = 1) (hb : d62934 q = 1) : d62650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54812, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54812, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54813 q = 1) (hb : d62934 q = 1) : d62651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54813, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54813, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54814 q = 1) (hb : d62934 q = 1) : d62652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54814, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54814, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54815 q = 1) (hb : d62934 q = 1) : d62653 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54815, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54815, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2190 (p : Pattern) (ha : d54821 p = 1) (hb : d62934 p = 1) : d62659 p = 1 := by
  have h0 (q : Pattern) (ha : d54774 q = 1) (hb : d62934 q = 1) : d62592 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54774, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2179 q ha hb
    | true =>
      simp only [d54774, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2181 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54783 q = 1) (hb : d62934 q = 1) : d62606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54783, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54783, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2183 q ha hb
  have h3 (q : Pattern) (ha : d54784 q = 1) (hb : d62934 q = 1) : d62607 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54784, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54784, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54793 q = 1) (hb : d62934 q = 1) : d62621 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54793, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54793, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2185 q ha hb
  have h5 (q : Pattern) (ha : d54794 q = 1) (hb : d62934 q = 1) : d62622 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54794, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54794, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54795 q = 1) (hb : d62934 q = 1) : d62623 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54795, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54795, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54804 q = 1) (hb : d62934 q = 1) : d62637 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54804, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54804, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2187 q ha hb
  have h8 (q : Pattern) (ha : d54805 q = 1) (hb : d62934 q = 1) : d62638 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54805, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54805, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54806 q = 1) (hb : d62934 q = 1) : d62639 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54806, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54806, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54807 q = 1) (hb : d62934 q = 1) : d62640 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54807, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54807, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54816 q = 1) (hb : d62934 q = 1) : d62654 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54816, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54816, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2189 q ha hb
  have h12 (q : Pattern) (ha : d54817 q = 1) (hb : d62934 q = 1) : d62655 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54817, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54817, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54818 q = 1) (hb : d62934 q = 1) : d62656 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54818, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54818, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54819 q = 1) (hb : d62934 q = 1) : d62657 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54819, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54819, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54820 q = 1) (hb : d62934 q = 1) : d62658 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54820, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54820, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54821 q = 1) (hb : d62934 q = 1) : d62659 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54821, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54821, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2191 (p : Pattern) (ha : d54827 p = 1) (hb : d62934 p = 1) : d62665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54822 q = 1) (hb : d62934 q = 1) : d62660 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54822, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2190 q ha hb
    | true =>
      simp only [d54822, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54823 q = 1) (hb : d62934 q = 1) : d62661 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54823, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54823, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54824 q = 1) (hb : d62934 q = 1) : d62662 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54824, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54824, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54825 q = 1) (hb : d62934 q = 1) : d62663 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54825, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54825, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54826 q = 1) (hb : d62934 q = 1) : d62664 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54826, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54826, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54827 q = 1) (hb : d62934 q = 1) : d62665 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54827, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54827, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2192 (p : Pattern) (ha : d54833 p = 1) (hb : d62934 p = 1) : d62671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54828 q = 1) (hb : d62934 q = 1) : d62666 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54828, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2191 q ha hb
    | true =>
      simp only [d54828, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54829 q = 1) (hb : d62934 q = 1) : d62667 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54829, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54829, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54830 q = 1) (hb : d62934 q = 1) : d62668 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54830, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54830, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54831 q = 1) (hb : d62934 q = 1) : d62669 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54831, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54831, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54832 q = 1) (hb : d62934 q = 1) : d62670 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54832, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54832, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54833 q = 1) (hb : d62934 q = 1) : d62671 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54833, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54833, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2193 (p : Pattern) (ha : d54839 p = 1) (hb : d62934 p = 1) : d62677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54834 q = 1) (hb : d62934 q = 1) : d62672 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54834, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2192 q ha hb
    | true =>
      simp only [d54834, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54835 q = 1) (hb : d62934 q = 1) : d62673 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54835, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54835, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54836 q = 1) (hb : d62934 q = 1) : d62674 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54836, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54836, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54837 q = 1) (hb : d62934 q = 1) : d62675 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54837, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54837, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54838 q = 1) (hb : d62934 q = 1) : d62676 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54838, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54838, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54839 q = 1) (hb : d62934 q = 1) : d62677 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54839, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54839, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2194 (p : Pattern) (ha : d54845 p = 1) (hb : d62934 p = 1) : d62683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54840 q = 1) (hb : d62934 q = 1) : d62678 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54840, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2193 q ha hb
    | true =>
      simp only [d54840, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54841 q = 1) (hb : d62934 q = 1) : d62679 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54841, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54841, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54842 q = 1) (hb : d62934 q = 1) : d62680 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54842, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54842, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54843 q = 1) (hb : d62934 q = 1) : d62681 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54843, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54843, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54844 q = 1) (hb : d62934 q = 1) : d62682 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54844, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54844, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54845 q = 1) (hb : d62934 q = 1) : d62683 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54845, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54845, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2195 (p : Pattern) (ha : d54851 p = 1) (hb : d62934 p = 1) : d62689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54846 q = 1) (hb : d62934 q = 1) : d62684 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54846, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2194 q ha hb
    | true =>
      simp only [d54846, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54847 q = 1) (hb : d62934 q = 1) : d62685 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54847, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54847, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54848 q = 1) (hb : d62934 q = 1) : d62686 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54848, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54848, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54849 q = 1) (hb : d62934 q = 1) : d62687 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54849, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54849, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54850 q = 1) (hb : d62934 q = 1) : d62688 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54850, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54850, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54851 q = 1) (hb : d62934 q = 1) : d62689 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54851, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54851, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2196 (p : Pattern) (ha : d54857 p = 1) (hb : d62934 p = 1) : d62695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54852 q = 1) (hb : d62934 q = 1) : d62690 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54852, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2195 q ha hb
    | true =>
      simp only [d54852, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54853 q = 1) (hb : d62934 q = 1) : d62691 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54853, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54853, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54854 q = 1) (hb : d62934 q = 1) : d62692 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54854, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54854, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54855 q = 1) (hb : d62934 q = 1) : d62693 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54855, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54855, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54856 q = 1) (hb : d62934 q = 1) : d62694 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54856, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54856, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54857 q = 1) (hb : d62934 q = 1) : d62695 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54857, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54857, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2197 (p : Pattern) (ha : d54863 p = 1) (hb : d62934 p = 1) : d62701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54858 q = 1) (hb : d62934 q = 1) : d62696 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54858, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2196 q ha hb
    | true =>
      simp only [d54858, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54859 q = 1) (hb : d62934 q = 1) : d62697 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54859, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54859, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54860 q = 1) (hb : d62934 q = 1) : d62698 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54860, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54860, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54861 q = 1) (hb : d62934 q = 1) : d62699 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54861, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54861, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54862 q = 1) (hb : d62934 q = 1) : d62700 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54862, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54862, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54863 q = 1) (hb : d62934 q = 1) : d62701 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54863, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54863, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2198 (p : Pattern) (ha : d54865 p = 1) (hb : d62934 p = 1) : d62704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d54978 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d54978 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d54978 q = 1) : d2527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d54978 q = 1) : d62702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54864 q = 1) (hb : d62934 q = 1) : d62703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, d62934, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54864, d62934, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54865 q = 1) (hb : d62934 q = 1) : d62704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54865, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2199 (p : Pattern) (ha : d54872 p = 1) (hb : d62934 p = 1) : d62712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d54978 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d54978 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d54978 q = 1) : d2539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d54978 q = 1) : d62710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54871 q = 1) (hb : d62934 q = 1) : d62711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, d62934, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54871, d62934, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54872 q = 1) (hb : d62934 q = 1) : d62712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54872, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2200 (p : Pattern) (ha : d54878 p = 1) (hb : d62934 p = 1) : d62718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d62934 q = 1) : d62705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2198 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d62934 q = 1) : d62706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d62934 q = 1) : d62707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d62934 q = 1) : d62708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d62934 q = 1) : d62709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d62934 q = 1) : d62713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2199 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d62934 q = 1) : d62714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d62934 q = 1) : d62715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d62934 q = 1) : d62716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d62934 q = 1) : d62717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d62934 q = 1) : d62718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54878, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2201 (p : Pattern) (ha : d54880 p = 1) (hb : d62934 p = 1) : d62721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d54978 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d54978 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d54978 q = 1) : d2552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d54978 q = 1) : d62719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54879 q = 1) (hb : d62934 q = 1) : d62720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, d62934, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54879, d62934, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54880 q = 1) (hb : d62934 q = 1) : d62721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54880, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2202 (p : Pattern) (ha : d54886 p = 1) (hb : d62934 p = 1) : d62727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d62934 q = 1) : d62722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2201 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d62934 q = 1) : d62723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d62934 q = 1) : d62724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d62934 q = 1) : d62725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d62934 q = 1) : d62726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d62934 q = 1) : d62727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2203 (p : Pattern) (ha : d54889 p = 1) (hb : d62934 p = 1) : d62731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d54978 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d54978 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d54978 q = 1) : d2566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d54978 q = 1) : d62729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54888 q = 1) (hb : d62934 q = 1) : d62730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, d62934, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54888, d62934, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54889 q = 1) (hb : d62934 q = 1) : d62731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54889, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2204 (p : Pattern) (ha : d54895 p = 1) (hb : d62934 p = 1) : d62737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d62934 q = 1) : d62732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2203 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d62934 q = 1) : d62733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d62934 q = 1) : d62734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d62934 q = 1) : d62735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d62934 q = 1) : d62736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d62934 q = 1) : d62737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2205 (p : Pattern) (ha : d54899 p = 1) (hb : d62934 p = 1) : d62742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d54978 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d54978 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d54978 q = 1) : d2581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d54978 q = 1) : d62740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54898 q = 1) (hb : d62934 q = 1) : d62741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, d62934, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54898, d62934, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54899 q = 1) (hb : d62934 q = 1) : d62742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54899, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2206 (p : Pattern) (ha : d54905 p = 1) (hb : d62934 p = 1) : d62748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d62934 q = 1) : d62743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2205 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d62934 q = 1) : d62744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d62934 q = 1) : d62745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d62934 q = 1) : d62746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d62934 q = 1) : d62747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d62934 q = 1) : d62748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2207 (p : Pattern) (ha : d54910 p = 1) (hb : d62934 p = 1) : d62754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d54978 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d54978 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d54978 q = 1) : d2597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d54978 q = 1) : d62752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54909 q = 1) (hb : d62934 q = 1) : d62753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, d62934, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54909, d62934, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54910 q = 1) (hb : d62934 q = 1) : d62754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54910, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2208 (p : Pattern) (ha : d54916 p = 1) (hb : d62934 p = 1) : d62760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d62934 q = 1) : d62755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2207 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d62934 q = 1) : d62756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d62934 q = 1) : d62757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d62934 q = 1) : d62758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d62934 q = 1) : d62759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d62934 q = 1) : d62760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2209 (p : Pattern) (ha : d54922 p = 1) (hb : d62934 p = 1) : d62767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d54978 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d54978 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d54978 q = 1) : d2614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d54978 q = 1) : d62765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54921 q = 1) (hb : d62934 q = 1) : d62766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, d62934, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54921, d62934, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54922 q = 1) (hb : d62934 q = 1) : d62767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54922, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2210 (p : Pattern) (ha : d54928 p = 1) (hb : d62934 p = 1) : d62773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d62934 q = 1) : d62768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2209 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d62934 q = 1) : d62769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d62934 q = 1) : d62770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d62934 q = 1) : d62771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d62934 q = 1) : d62772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d62934 q = 1) : d62773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2211 (p : Pattern) (ha : d54934 p = 1) (hb : d62934 p = 1) : d62779 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d62934 q = 1) : d62728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2200 q ha hb
    | true =>
      simp only [d54887, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2202 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d62934 q = 1) : d62738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2204 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d62934 q = 1) : d62739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d62934 q = 1) : d62749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2206 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d62934 q = 1) : d62750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d62934 q = 1) : d62751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d62934 q = 1) : d62761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2208 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d62934 q = 1) : d62762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d62934 q = 1) : d62763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d62934 q = 1) : d62764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d62934 q = 1) : d62774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2210 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d62934 q = 1) : d62775 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d62934 q = 1) : d62776 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d62934 q = 1) : d62777 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d62934 q = 1) : d62778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d62934 q = 1) : d62779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2212 (p : Pattern) (ha : d54940 p = 1) (hb : d62934 p = 1) : d62785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d62934 q = 1) : d62780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2211 q ha hb
    | true =>
      simp only [d54935, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d62934 q = 1) : d62781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d62934 q = 1) : d62782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d62934 q = 1) : d62783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d62934 q = 1) : d62784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d62934 q = 1) : d62785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2213 (p : Pattern) (ha : d54946 p = 1) (hb : d62934 p = 1) : d62791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d62934 q = 1) : d62786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2212 q ha hb
    | true =>
      simp only [d54941, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d62934 q = 1) : d62787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d62934 q = 1) : d62788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d62934 q = 1) : d62789 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d62934 q = 1) : d62790 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d62934 q = 1) : d62791 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2214 (p : Pattern) (ha : d54952 p = 1) (hb : d62934 p = 1) : d62797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d62934 q = 1) : d62792 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2213 q ha hb
    | true =>
      simp only [d54947, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d62934 q = 1) : d62793 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d62934 q = 1) : d62794 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d62934 q = 1) : d62795 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d62934 q = 1) : d62796 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d62934 q = 1) : d62797 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2215 (p : Pattern) (ha : d54958 p = 1) (hb : d62934 p = 1) : d62803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d62934 q = 1) : d62798 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2214 q ha hb
    | true =>
      simp only [d54953, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d62934 q = 1) : d62799 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d62934 q = 1) : d62800 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d62934 q = 1) : d62801 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d62934 q = 1) : d62802 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d62934 q = 1) : d62803 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2216 (p : Pattern) (ha : d54964 p = 1) (hb : d62934 p = 1) : d62809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d62934 q = 1) : d62804 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2215 q ha hb
    | true =>
      simp only [d54959, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d62934 q = 1) : d62805 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d62934 q = 1) : d62806 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d62934 q = 1) : d62807 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d62934 q = 1) : d62808 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d62934 q = 1) : d62809 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2217 (p : Pattern) (ha : d54970 p = 1) (hb : d62934 p = 1) : d62815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d62934 q = 1) : d62810 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2216 q ha hb
    | true =>
      simp only [d54965, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d62934 q = 1) : d62811 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d62934 q = 1) : d62812 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d62934 q = 1) : d62813 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d62934 q = 1) : d62814 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d62934 q = 1) : d62815 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2218 (p : Pattern) (ha : d54976 p = 1) (hb : d62934 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d62934 q = 1) : d62816 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2217 q ha hb
    | true =>
      simp only [d54971, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d62934 q = 1) : d62817 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d62934 q = 1) : d62818 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d62934 q = 1) : d62819 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d62934 q = 1) : d62820 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d62934 q = 1) : d62821 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2219 (p : Pattern) (ha : d42 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2220 (p : Pattern) (ha : d48 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d45 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d46 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d48 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2221 (p : Pattern) (ha : d55 p = 1) (hb : d62938 p = 1) : d60 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54 q = 1) (hb : d62936 q = 1) : d54 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d55 q = 1) (hb : d62938 q = 1) : d60 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, d62938, d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55, d62938, d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2222 (p : Pattern) (ha : d2520 p = 1) (hb : d62939 p = 1) : d63625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d62938 q = 1) : d61 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2220 q ha hb
    | true =>
      simp only [d56, d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2221 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d62938 q = 1) : d62 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d62938 q = 1) : d63 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d62938 q = 1) : d63623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d63623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d63623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2519 q = 1) (hb : d62939 q = 1) : d63624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, d62939, d63624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2519, d62939, d63624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2520 q = 1) (hb : d62939 q = 1) : d63625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, d63625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2520, d63625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2223 (p : Pattern) (ha : d104 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2224 (p : Pattern) (ha : d111 p = 1) (hb : d62938 p = 1) : d406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d110 q = 1) (hb : d62936 q = 1) : d110 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d111 q = 1) (hb : d62938 q = 1) : d406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d62938, d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d111, d62938, d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2225 (p : Pattern) (ha : d213 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d213 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d213, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2226 (p : Pattern) (ha : d116 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d116 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2227 (p : Pattern) (ha : d123 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2228 (p : Pattern) (ha : d156 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2229 (p : Pattern) (ha : d51643 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d117 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2226 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2227 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d157 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
  have h10 (q : Pattern) (ha : d4335 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4336 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51641 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51642 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51643 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2230 (p : Pattern) (ha : d51646 p = 1) (hb : d62938 p = 1) : d63631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51645 q = 1) (hb : d62936 q = 1) : d51645 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51646 q = 1) (hb : d62938 q = 1) : d63631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d62938, d63631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51646, d62938, d63631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2231 (p : Pattern) (ha : d54752 p = 1) (hb : d62939 p = 1) : d63637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2223 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d62938 q = 1) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2223 q ha hb
    | true =>
      simp only [d112, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2224 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d62938 q = 1) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d62938 q = 1) : d63630 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d63630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d63630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d62938 q = 1) : d63632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d63632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2229 q ha hb
    | true =>
      simp only [d51647, d63632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2230 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2225 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d62938 q = 1) : d63633 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d63633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d63633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d62938 q = 1) : d63634 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d63634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d63634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d62938 q = 1) : d63635 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d63635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d63635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54751 q = 1) (hb : d62939 q = 1) : d63636 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54751, d62939, d63636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54751, d62939, d63636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54752 q = 1) (hb : d62939 q = 1) : d63637 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54752, d63637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54752, d63637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2232 (p : Pattern) (ha : d284 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2233 (p : Pattern) (ha : d291 p = 1) (hb : d62938 p = 1) : d53655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290 q = 1) (hb : d62936 q = 1) : d290 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d291 q = 1) (hb : d62938 q = 1) : d53655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d62938, d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d291, d62938, d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2234 (p : Pattern) (ha : d397 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d283 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d397 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d397, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2235 (p : Pattern) (ha : d296 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d296 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2236 (p : Pattern) (ha : d303 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2237 (p : Pattern) (ha : d336 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d336 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2238 (p : Pattern) (ha : d51660 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2235 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2226 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2236 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2227 q ha hb
  have h7 (q : Pattern) (ha : d305 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d337 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2237 q ha hb
    | true =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d370 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d371 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4372 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51658 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51659 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51660 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2239 (p : Pattern) (ha : d51663 p = 1) (hb : d62938 p = 1) : d63644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51662 q = 1) (hb : d62936 q = 1) : d51662 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51663 q = 1) (hb : d62938 q = 1) : d63644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d62938, d63644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51663, d62938, d63644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2240 (p : Pattern) (ha : d54759 p = 1) (hb : d62939 p = 1) : d63650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2232 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d62938 q = 1) : d53656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2232 q ha hb
    | true =>
      simp only [d292, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2233 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d62938 q = 1) : d53657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d62938 q = 1) : d63643 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d63643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d63643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d62938 q = 1) : d63645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d63645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2238 q ha hb
    | true =>
      simp only [d51664, d63645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2239 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d62938 q = 1) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2234 q ha hb
    | true =>
      simp only [d398, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2224 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d62938 q = 1) : d63646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d63646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d63646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d62938 q = 1) : d63647 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d63647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d63647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d62938 q = 1) : d63648 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d63648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d63648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54758 q = 1) (hb : d62939 q = 1) : d63649 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54758, d62939, d63649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54758, d62939, d63649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54759 q = 1) (hb : d62939 q = 1) : d63650 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54759, d63650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54759, d63650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2241 (p : Pattern) (ha : d54765 p = 1) (hb : d62939 p = 1) : d63656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d62939 q = 1) : d63626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, d63626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, d63626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2222 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d62939 q = 1) : d63627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, d63627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, d63627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d62939 q = 1) : d63628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, d63628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, d63628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d62939 q = 1) : d63629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, d63629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, d63629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54753 q = 1) (hb : d62939 q = 1) : d63638 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54753, d63638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54753, d63638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2231 q ha hb
  have h6 (q : Pattern) (ha : d54754 q = 1) (hb : d62939 q = 1) : d63639 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54754, d63639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54754, d63639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54755 q = 1) (hb : d62939 q = 1) : d63640 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54755, d63640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54755, d63640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54756 q = 1) (hb : d62939 q = 1) : d63641 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54756, d63641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54756, d63641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54757 q = 1) (hb : d62939 q = 1) : d63642 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54757, d63642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54757, d63642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54760 q = 1) (hb : d62939 q = 1) : d63651 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54760, d63651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54760, d63651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2240 q ha hb
  have h11 (q : Pattern) (ha : d54761 q = 1) (hb : d62939 q = 1) : d63652 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54761, d63652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54761, d63652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54762 q = 1) (hb : d62939 q = 1) : d63653 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54762, d63653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54762, d63653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54763 q = 1) (hb : d62939 q = 1) : d63654 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54763, d63654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54763, d63654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54764 q = 1) (hb : d62939 q = 1) : d63655 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54764, d63655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54764, d63655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54765 q = 1) (hb : d62939 q = 1) : d63656 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54765, d63656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54765, d63656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2242 (p : Pattern) (ha : d487 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d487 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2243 (p : Pattern) (ha : d491 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d491 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2244 (p : Pattern) (ha : d497 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
    | true =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2243 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d497 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2245 (p : Pattern) (ha : d507 p = 1) (hb : d62938 p = 1) : d53680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d506 q = 1) (hb : d62936 q = 1) : d506 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d507 q = 1) (hb : d62938 q = 1) : d53680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d62938, d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d507, d62938, d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2246 (p : Pattern) (ha : d638 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d633 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2243 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d634 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d635 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d636 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d637 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d638 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d638, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2247 (p : Pattern) (ha : d644 p = 1) (hb : d62938 p = 1) : d653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d643 q = 1) (hb : d62936 q = 1) : d643 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d644 q = 1) (hb : d62938 q = 1) : d653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d62938, d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d644, d62938, d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2248 (p : Pattern) (ha : d512 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d511 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d512 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2249 (p : Pattern) (ha : d514 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d514 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
end NetHack.Soko22Hazard87
