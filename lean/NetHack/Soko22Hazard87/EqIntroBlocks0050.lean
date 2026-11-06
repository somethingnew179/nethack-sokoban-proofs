import NetHack.Soko22Hazard87.EqIntroBlocks0049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro12500 (p : Pattern) (selected : d143394 p = 0) : d144698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143289 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12474 q selected
    | true =>
      simp only [d143289, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143290 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143290, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143295 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143295, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143329 q = 0) : d144658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143329, d144658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143329, d144658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143330 q = 0) : d144659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143330, d144659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143330, d144659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143394 q = 0) : d144698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143394, d144698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143394, d144698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12501 (p : Pattern) (selected : d143398 p = 0) : d144702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143344 q = 0) : d144673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143344, d144673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12487 q selected
    | true =>
      simp only [d143344, d144673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143345 q = 0) : d144674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143345, d144674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143345, d144674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143346 q = 0) : d144675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143346, d144675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143346, d144675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143347 q = 0) : d144676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143347, d144676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143347, d144676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143348 q = 0) : d144677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143348, d144677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143348, d144677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143398 q = 0) : d144702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143398, d144702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143398, d144702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12502 (p : Pattern) (selected : d143400 p = 0) : d144636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143361 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143361, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12491 q selected
    | true =>
      simp only [d143361, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143362 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143362, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143362, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143365 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12492 q selected
    | true =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143366 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143367 q = 0) : d144620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143367, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143367, d144620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143368 q = 0) : d144621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143368, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143368, d144621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143369 q = 0) : d144622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143369, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143369, d144622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143400 q = 0) : d144636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143400, d144636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143400, d144636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12503 (p : Pattern) (selected : d143401 p = 0) : d144637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143365 q = 0) : d144618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12492 q selected
    | true =>
      simp only [d143365, d144618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143366 q = 0) : d144619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, d144619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143371 q = 0) : d144624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143371, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143371, d144624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143372 q = 0) : d144625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143372, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143372, d144625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143373 q = 0) : d144626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143373, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143373, d144626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143401 q = 0) : d144637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143401, d144637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143401, d144637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12504 (p : Pattern) (selected : d143404 p = 0) : d144705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143285 q = 0) : d144614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12473 q selected
    | true =>
      simp only [d143285, d144614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143286 q = 0) : d144615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143286, d144615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143377 q = 0) : d144681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143377, d144681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143377, d144681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143378 q = 0) : d144682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143378, d144682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143378, d144682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143379 q = 0) : d144683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143379, d144683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143379, d144683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143404 q = 0) : d144705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143404, d144705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143404, d144705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12505 (p : Pattern) (selected : d143410 p = 0) : d144711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143322 q = 0) : d144651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143322, d144651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12481 q selected
    | true =>
      simp only [d143322, d144651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12482 q selected
  have h2 (q : Pattern) (selected : d143323 q = 0) : d144652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143323, d144652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143323, d144652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143324 q = 0) : d144653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143324, d144653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143324, d144653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143325 q = 0) : d144654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143325, d144654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143325, d144654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143332 q = 0) : d144661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143332, d144661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12483 q selected
    | true =>
      simp only [d143332, d144661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12484 q selected
  have h6 (q : Pattern) (selected : d143333 q = 0) : d144662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143333, d144662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143333, d144662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143334 q = 0) : d144663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143334, d144663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143334, d144663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143350 q = 0) : d144679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143350, d144679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12488 q selected
    | true =>
      simp only [d143350, d144679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12475 q selected
  have h9 (q : Pattern) (selected : d143375 q = 0) : d144628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143375, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12493 q selected
    | true =>
      simp only [d143375, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12494 q selected
  have h10 (q : Pattern) (selected : d143376 q = 0) : d144680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143376, d144680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143376, d144680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143381 q = 0) : d144685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143381, d144685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12495 q selected
    | true =>
      simp only [d143381, d144685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143382 q = 0) : d144686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143382, d144686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143382, d144686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143383 q = 0) : d144687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143383, d144687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143383, d144687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143384 q = 0) : d144688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143384, d144688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143384, d144688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143385 q = 0) : d144689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143385, d144689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143385, d144689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143389 q = 0) : d144693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143389, d144693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12497 q selected
    | true =>
      simp only [d143389, d144693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12498 q selected
  have h17 (q : Pattern) (selected : d143390 q = 0) : d144694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143390, d144694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143390, d144694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143391 q = 0) : d144695 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143391, d144695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143391, d144695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d143392 q = 0) : d144696 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143392, d144696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143392, d144696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143395 q = 0) : d144699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143395, d144699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12499 q selected
    | true =>
      simp only [d143395, d144699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12500 q selected
  have h21 (q : Pattern) (selected : d143396 q = 0) : d144700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143396, d144700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143396, d144700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d143397 q = 0) : d144701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143397, d144701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143397, d144701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143399 q = 0) : d144703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143399, d144703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12501 q selected
    | true =>
      simp only [d143399, d144703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12478 q selected
  have h24 (q : Pattern) (selected : d143402 q = 0) : d144638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143402, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12502 q selected
    | true =>
      simp only [d143402, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12503 q selected
  have h25 (q : Pattern) (selected : d143403 q = 0) : d144704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143403, d144704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d143403, d144704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d143405 q = 0) : d144706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143405, d144706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12504 q selected
    | true =>
      simp only [d143405, d144706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d143406 q = 0) : d144707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143406, d144707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d143406, d144707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d143407 q = 0) : d144708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143407, d144708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d143407, d144708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d143408 q = 0) : d144709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143408, d144709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d143408, d144709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d143409 q = 0) : d144710 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143409, d144710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143409, d144710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d143410 q = 0) : d144711 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143410, d144711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143410, d144711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12506 (p : Pattern) (selected : d143417 p = 0) : d144718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143299 q = 0) : d144628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12475 q selected
    | true =>
      simp only [d143299, d144628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12476 q selected
  have h2 (q : Pattern) (selected : d143300 q = 0) : d144629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143300, d144629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143301 q = 0) : d144630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143301, d144630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143302 q = 0) : d144631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143302, d144631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143303 q = 0) : d144632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143303, d144632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143412 q = 0) : d144713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143412, d144713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12476 q selected
    | true =>
      simp only [d143412, d144713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143413 q = 0) : d144714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143413, d144714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143413, d144714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143414 q = 0) : d144715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143414, d144715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143414, d144715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143415 q = 0) : d144716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143415, d144716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143415, d144716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143416 q = 0) : d144717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143416, d144717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143416, d144717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143417 q = 0) : d144718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143417, d144718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143417, d144718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12507 (p : Pattern) (selected : d143423 p = 0) : d144724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143412 q = 0) : d144713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143412, d144713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12476 q selected
    | true =>
      simp only [d143412, d144713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143413 q = 0) : d144714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143413, d144714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143413, d144714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143414 q = 0) : d144715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143414, d144715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143414, d144715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143415 q = 0) : d144716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143415, d144716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143415, d144716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143416 q = 0) : d144717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143416, d144717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143416, d144717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143418 q = 0) : d144719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143418, d144719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12479 q selected
    | true =>
      simp only [d143418, d144719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143419 q = 0) : d144720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143419, d144720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143419, d144720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143420 q = 0) : d144721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143420, d144721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143420, d144721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143421 q = 0) : d144722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143421, d144722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143421, d144722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143422 q = 0) : d144723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143422, d144723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143422, d144723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143423 q = 0) : d144724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143423, d144724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143423, d144724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12508 (p : Pattern) (selected : d143430 p = 0) : d144731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143399 q = 0) : d144703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143399, d144703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12501 q selected
    | true =>
      simp only [d143399, d144703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12478 q selected
  have h2 (q : Pattern) (selected : d143402 q = 0) : d144638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143402, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12502 q selected
    | true =>
      simp only [d143402, d144638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12503 q selected
  have h3 (q : Pattern) (selected : d143403 q = 0) : d144704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143403, d144704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143403, d144704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143405 q = 0) : d144706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143405, d144706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12504 q selected
    | true =>
      simp only [d143405, d144706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143406 q = 0) : d144707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143406, d144707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143406, d144707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143407 q = 0) : d144708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143407, d144708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143407, d144708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143428 q = 0) : d144729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143428, d144729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143428, d144729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143429 q = 0) : d144730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143429, d144730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143429, d144730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143430 q = 0) : d144731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143430, d144731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143430, d144731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12509 (p : Pattern) (selected : d143432 p = 0) : d144733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143418 q = 0) : d144719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143418, d144719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12479 q selected
    | true =>
      simp only [d143418, d144719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143419 q = 0) : d144720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143419, d144720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143419, d144720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143420 q = 0) : d144721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143420, d144721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143420, d144721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143421 q = 0) : d144722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143421, d144722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143421, d144722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143422 q = 0) : d144723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143422, d144723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143422, d144723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143432 q = 0) : d144733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143432, d144733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143432, d144733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12510 (p : Pattern) (selected : d1383 p = 0) : d52871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1380 q = 0) : d52868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
  have h2 (q : Pattern) (selected : d1100 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1381 q = 0) : d52869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1101 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1382 q = 0) : d52870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1383 q = 0) : d52871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12511 (p : Pattern) (selected : d1388 p = 0) : d52876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1385 q = 0) : d52873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
  have h2 (q : Pattern) (selected : d1110 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1386 q = 0) : d52874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1111 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1387 q = 0) : d52875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1388 q = 0) : d52876 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12512 (p : Pattern) (selected : d1394 p = 0) : d52882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1391 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1393 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1394 q = 0) : d52882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12513 (p : Pattern) (selected : d13167 p = 0) : d113459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13164 q = 0) : d113456 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
  have h2 (q : Pattern) (selected : d13025 q = 0) : d113355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8289 q selected
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13165 q = 0) : d113457 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13026 q = 0) : d113356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13166 q = 0) : d113458 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13167 q = 0) : d113459 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12514 (p : Pattern) (selected : d143453 p = 0) : d144754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143438 q = 0) : d144739 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143438, d144739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12510 q selected
    | true =>
      simp only [d143438, d144739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12511 q selected
  have h2 (q : Pattern) (selected : d143439 q = 0) : d144740 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143439, d144740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143439, d144740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143440 q = 0) : d144741 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143440, d144741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143440, d144741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143441 q = 0) : d144742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143441, d144742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12511 q selected
    | true =>
      simp only [d143441, d144742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12513 q selected
  have h5 (q : Pattern) (selected : d143442 q = 0) : d144743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143442, d144743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143442, d144743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143443 q = 0) : d144744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143443, d144744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143443, d144744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143444 q = 0) : d144745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143444, d144745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143444, d144745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143445 q = 0) : d144746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143445, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12511 q selected
    | true =>
      simp only [d143445, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12512 q selected
  have h9 (q : Pattern) (selected : d143446 q = 0) : d144747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143446, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143446, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143447 q = 0) : d144748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143447, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143447, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143448 q = 0) : d144749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12512 q selected
    | true =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143449 q = 0) : d144750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143450 q = 0) : d144751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143451 q = 0) : d144752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143451, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143451, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143452 q = 0) : d144753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143452, d144753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143452, d144753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143453 q = 0) : d144754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143453, d144754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143453, d144754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12515 (p : Pattern) (selected : d143458 p = 0) : d144759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143445 q = 0) : d144746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143445, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12511 q selected
    | true =>
      simp only [d143445, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12512 q selected
  have h2 (q : Pattern) (selected : d143446 q = 0) : d144747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143446, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143446, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143447 q = 0) : d144748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143447, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143447, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143448 q = 0) : d144749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12512 q selected
    | true =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143449 q = 0) : d144750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143450 q = 0) : d144751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143451 q = 0) : d144752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143451, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143451, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143456 q = 0) : d144757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143456, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143456, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143457 q = 0) : d144758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143457, d144758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143457, d144758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143458 q = 0) : d144759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143458, d144759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143458, d144759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12516 (p : Pattern) (selected : d143464 p = 0) : d144765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143454 q = 0) : d144755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143454, d144755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12514 q selected
    | true =>
      simp only [d143454, d144755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143455 q = 0) : d144756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143455, d144756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143455, d144756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143459 q = 0) : d144760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12515 q selected
    | true =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143460 q = 0) : d144761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143461 q = 0) : d144762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143461, d144762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143461, d144762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143462 q = 0) : d144763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143462, d144763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143462, d144763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143463 q = 0) : d144764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143463, d144764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143463, d144764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143464 q = 0) : d144765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143464, d144765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143464, d144765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12517 (p : Pattern) (selected : d143466 p = 0) : d144767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143448 q = 0) : d144749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12512 q selected
    | true =>
      simp only [d143448, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143449 q = 0) : d144750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143449, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143450 q = 0) : d144751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143450, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143456 q = 0) : d144757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143456, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143456, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143465 q = 0) : d144766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143465, d144766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143465, d144766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143466 q = 0) : d144767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143466, d144767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143466, d144767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12518 (p : Pattern) (selected : d143472 p = 0) : d144773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143459 q = 0) : d144760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12515 q selected
    | true =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143460 q = 0) : d144761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143467 q = 0) : d144768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143467, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12517 q selected
    | true =>
      simp only [d143467, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143468 q = 0) : d144769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143468, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143468, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143469 q = 0) : d144770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143469, d144770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143469, d144770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143470 q = 0) : d144771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143470, d144771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143470, d144771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143471 q = 0) : d144772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143471, d144772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143471, d144772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143472 q = 0) : d144773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143472, d144773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143472, d144773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12519 (p : Pattern) (selected : d1445 p = 0) : d52876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1442 q = 0) : d52873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, d52873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
  have h2 (q : Pattern) (selected : d1265 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 0) : d52874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, d52874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 0) : d52875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, d52875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1445 q = 0) : d52876 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1445, d52876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1445, d52876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12520 (p : Pattern) (selected : d1450 p = 0) : d52882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1447 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h2 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1450 q = 0) : d52882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, d52882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1450, d52882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12521 (p : Pattern) (selected : d143483 p = 0) : d144759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143474 q = 0) : d144746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143474, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12519 q selected
    | true =>
      simp only [d143474, d144746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12520 q selected
  have h2 (q : Pattern) (selected : d143475 q = 0) : d144747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143475, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143475, d144747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143476 q = 0) : d144748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143476, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143476, d144748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143477 q = 0) : d144749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143477, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12520 q selected
    | true =>
      simp only [d143477, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143478 q = 0) : d144750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143478, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143478, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143479 q = 0) : d144751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143479, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143479, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143480 q = 0) : d144752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143480, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143480, d144752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143481 q = 0) : d144757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143481, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143481, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143482 q = 0) : d144758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143482, d144758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143482, d144758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143483 q = 0) : d144759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143483, d144759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143483, d144759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12522 (p : Pattern) (selected : d143487 p = 0) : d144767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143477 q = 0) : d144749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143477, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12520 q selected
    | true =>
      simp only [d143477, d144749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143478 q = 0) : d144750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143478, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143478, d144750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143479 q = 0) : d144751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143479, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143479, d144751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143481 q = 0) : d144757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143481, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143481, d144757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143486 q = 0) : d144766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143486, d144766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143486, d144766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143487 q = 0) : d144767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143487, d144767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143487, d144767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12523 (p : Pattern) (selected : d143493 p = 0) : d144773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143484 q = 0) : d144760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143484, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12521 q selected
    | true =>
      simp only [d143484, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143485 q = 0) : d144761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143485, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143485, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143488 q = 0) : d144768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143488, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12522 q selected
    | true =>
      simp only [d143488, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143489 q = 0) : d144769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143489, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143489, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143490 q = 0) : d144770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143490, d144770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143490, d144770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143491 q = 0) : d144771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143491, d144771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143491, d144771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143492 q = 0) : d144772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143492, d144772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143492, d144772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143493 q = 0) : d144773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143493, d144773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143493, d144773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12524 (p : Pattern) (selected : d143497 p = 0) : d144778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143488 q = 0) : d144768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143488, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12522 q selected
    | true =>
      simp only [d143488, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143489 q = 0) : d144769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143489, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143489, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143494 q = 0) : d144775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143494, d144775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143494, d144775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143495 q = 0) : d144776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143495, d144776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143495, d144776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143496 q = 0) : d144777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143496, d144777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143496, d144777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143497 q = 0) : d144778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143497, d144778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143497, d144778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12525 (p : Pattern) (selected : d143503 p = 0) : d144784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143459 q = 0) : d144760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12515 q selected
    | true =>
      simp only [d143459, d144760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143460 q = 0) : d144761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143460, d144761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143500 q = 0) : d144781 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143500, d144781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143500, d144781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143501 q = 0) : d144782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143501, d144782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143501, d144782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143502 q = 0) : d144783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143502, d144783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143502, d144783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143503 q = 0) : d144784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143503, d144784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143503, d144784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12526 (p : Pattern) (selected : d143509 p = 0) : d144790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143473 q = 0) : d144774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143473, d144774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12516 q selected
    | true =>
      simp only [d143473, d144774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12518 q selected
  have h2 (q : Pattern) (selected : d143498 q = 0) : d144779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143498, d144779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12523 q selected
    | true =>
      simp only [d143498, d144779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12524 q selected
  have h3 (q : Pattern) (selected : d143499 q = 0) : d144780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143499, d144780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143499, d144780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143504 q = 0) : d144785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143504, d144785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12525 q selected
    | true =>
      simp only [d143504, d144785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143505 q = 0) : d144786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143505, d144786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143505, d144786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143506 q = 0) : d144787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143506, d144787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143506, d144787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143507 q = 0) : d144788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143507, d144788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143507, d144788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143508 q = 0) : d144789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143508, d144789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143508, d144789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143509 q = 0) : d144790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143509, d144790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143509, d144790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12527 (p : Pattern) (selected : d143514 p = 0) : d144778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143467 q = 0) : d144768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143467, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12517 q selected
    | true =>
      simp only [d143467, d144768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143468 q = 0) : d144769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143468, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143468, d144769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143511 q = 0) : d144775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143511, d144775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143511, d144775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143512 q = 0) : d144776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143512, d144776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143512, d144776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143513 q = 0) : d144777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143513, d144777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143513, d144777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143514 q = 0) : d144778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143514, d144778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143514, d144778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12528 (p : Pattern) (selected : d143520 p = 0) : d144797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143515 q = 0) : d144792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143515, d144792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12527 q selected
    | true =>
      simp only [d143515, d144792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143516 q = 0) : d144793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143516, d144793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143516, d144793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143517 q = 0) : d144794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143517, d144794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143517, d144794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143518 q = 0) : d144795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143518, d144795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143518, d144795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143519 q = 0) : d144796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143519, d144796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143519, d144796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143520 q = 0) : d144797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143520, d144797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143520, d144797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12529 (p : Pattern) (selected : d143526 p = 0) : d144803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143305 q = 0) : d144634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143305, d144634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143305, d144634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12477 q selected
  have h2 (q : Pattern) (selected : d143306 q = 0) : d144635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143306, d144635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143306, d144635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d143315 q = 0) : d144644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143315, d144644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12477 q selected
    | true =>
      simp only [d143315, d144644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12480 q selected
  have h4 (q : Pattern) (selected : d143316 q = 0) : d144645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143316, d144645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143316, d144645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143317 q = 0) : d144646 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143317, d144646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143317, d144646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143411 q = 0) : d144712 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143411, d144712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12496 q selected
    | true =>
      simp only [d143411, d144712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12505 q selected
  have h7 (q : Pattern) (selected : d143424 q = 0) : d144725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143424, d144725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12506 q selected
    | true =>
      simp only [d143424, d144725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12507 q selected
  have h8 (q : Pattern) (selected : d143425 q = 0) : d144726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143425, d144726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143425, d144726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143426 q = 0) : d144727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143426, d144727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143426, d144727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d143427 q = 0) : d144728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143427, d144728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143427, d144728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143431 q = 0) : d144732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143431, d144732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143431, d144732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12508 q selected
  have h12 (q : Pattern) (selected : d143433 q = 0) : d144734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143433, d144734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143433, d144734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12509 q selected
  have h13 (q : Pattern) (selected : d143434 q = 0) : d144735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143434, d144735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143434, d144735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143435 q = 0) : d144736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143435, d144736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143435, d144736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d143436 q = 0) : d144737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143436, d144737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d143436, d144737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d143437 q = 0) : d144738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143437, d144738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143437, d144738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143510 q = 0) : d144791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143510, d144791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143510, d144791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12526 q selected
  have h18 (q : Pattern) (selected : d143521 q = 0) : d144798 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143521, d144798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143521, d144798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12528 q selected
  have h19 (q : Pattern) (selected : d143522 q = 0) : d144799 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143522, d144799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143522, d144799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143523 q = 0) : d144800 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143523, d144800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143523, d144800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d143524 q = 0) : d144801 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143524, d144801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d143524, d144801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d143525 q = 0) : d144802 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143525, d144802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143525, d144802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143526 q = 0) : d144803 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143526, d144803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143526, d144803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro12530 (p : Pattern) (selected : d143532 p = 0) : d144809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143527 q = 0) : d144804 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143527, d144804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143527, d144804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12529 q selected
  have h2 (q : Pattern) (selected : d143528 q = 0) : d144805 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143528, d144805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143528, d144805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143529 q = 0) : d144806 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143529, d144806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143529, d144806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143530 q = 0) : d144807 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143530, d144807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143530, d144807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143531 q = 0) : d144808 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143531, d144808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143531, d144808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143532 q = 0) : d144809 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143532, d144809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143532, d144809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12531 (p : Pattern) (selected : d1573 p = 0) : d53014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1571 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1572 q = 0) : d53013 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1573 q = 0) : d53014 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12532 (p : Pattern) (selected : d1585 p = 0) : d53026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1584 q = 0) : d53025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1585 q = 0) : d53026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12533 (p : Pattern) (selected : d143545 p = 0) : d144822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143536 q = 0) : d144813 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143536, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12531 q selected
    | true =>
      simp only [d143536, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12532 q selected
  have h2 (q : Pattern) (selected : d143537 q = 0) : d144814 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143537, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143537, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143538 q = 0) : d144815 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143538, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143538, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143539 q = 0) : d144816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12532 q selected
    | true =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143540 q = 0) : d144817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143541 q = 0) : d144818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143542 q = 0) : d144819 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143542, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143542, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143543 q = 0) : d144820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143543, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143543, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143544 q = 0) : d144821 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143544, d144821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143544, d144821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143545 q = 0) : d144822 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143545, d144822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143545, d144822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12534 (p : Pattern) (selected : d143549 p = 0) : d144826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143539 q = 0) : d144816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12532 q selected
    | true =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143540 q = 0) : d144817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143541 q = 0) : d144818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143543 q = 0) : d144820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143543, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143543, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143548 q = 0) : d144825 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143548, d144825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143548, d144825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143549 q = 0) : d144826 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143549, d144826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143549, d144826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12535 (p : Pattern) (selected : d143555 p = 0) : d144832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143553 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143554 q = 0) : d144831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143554, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143554, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143555 q = 0) : d144832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143555, d144832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143555, d144832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12536 (p : Pattern) (selected : d143559 p = 0) : d144836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143557 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143558 q = 0) : d144835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143558, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143558, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143559 q = 0) : d144836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143559, d144836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143559, d144836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12537 (p : Pattern) (selected : d143565 p = 0) : d144842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143560 q = 0) : d144837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12535 q selected
    | true =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12536 q selected
  have h2 (q : Pattern) (selected : d143561 q = 0) : d144838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143562 q = 0) : d144839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143563 q = 0) : d144840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143564 q = 0) : d144841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143565 q = 0) : d144842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143565, d144842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143565, d144842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12538 (p : Pattern) (selected : d143568 p = 0) : d144845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143553 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143554 q = 0) : d144831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143554, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143554, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143568 q = 0) : d144845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143568, d144845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143568, d144845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12539 (p : Pattern) (selected : d143569 p = 0) : d144846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143557 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143558 q = 0) : d144835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143558, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143558, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143569 q = 0) : d144846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143569, d144846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143569, d144846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12540 (p : Pattern) (selected : d143575 p = 0) : d144852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143560 q = 0) : d144837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12535 q selected
    | true =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12536 q selected
  have h2 (q : Pattern) (selected : d143561 q = 0) : d144838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143562 q = 0) : d144839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143563 q = 0) : d144840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143564 q = 0) : d144841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143570 q = 0) : d144847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143570, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12538 q selected
    | true =>
      simp only [d143570, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12539 q selected
  have h7 (q : Pattern) (selected : d143571 q = 0) : d144848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143571, d144848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143571, d144848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143572 q = 0) : d144849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143572, d144849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143572, d144849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143573 q = 0) : d144850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143573, d144850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143573, d144850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143574 q = 0) : d144851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143574, d144851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143574, d144851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143575 q = 0) : d144852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143575, d144852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143575, d144852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12541 (p : Pattern) (selected : d143580 p = 0) : d144857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143553 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143579 q = 0) : d144856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143579, d144856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143579, d144856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143580 q = 0) : d144857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143580, d144857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143580, d144857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12542 (p : Pattern) (selected : d143582 p = 0) : d144859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143557 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143581 q = 0) : d144858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143581, d144858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143581, d144858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143582 q = 0) : d144859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143582, d144859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143582, d144859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12543 (p : Pattern) (selected : d143589 p = 0) : d144866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143587 q = 0) : d144864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143587, d144864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143587, d144864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143588 q = 0) : d144865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143588, d144865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143588, d144865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143589 q = 0) : d144866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143589, d144866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143589, d144866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12544 (p : Pattern) (selected : d143592 p = 0) : d144869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143590 q = 0) : d144867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143590, d144867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143590, d144867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143591 q = 0) : d144868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143591, d144868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143591, d144868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143592 q = 0) : d144869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143592, d144869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143592, d144869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12545 (p : Pattern) (selected : d1558 p = 0) : d52999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1556 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1557 q = 0) : d52998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1558 q = 0) : d52999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12546 (p : Pattern) (selected : d13354 p = 0) : d113614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13351 q = 0) : d113611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13352 q = 0) : d113612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13353 q = 0) : d113613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13354 q = 0) : d113614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12547 (p : Pattern) (selected : d143604 p = 0) : d144881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143596 q = 0) : d144873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143596, d144873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12545 q selected
    | true =>
      simp only [d143596, d144873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12531 q selected
  have h2 (q : Pattern) (selected : d143597 q = 0) : d144874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143597, d144874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143597, d144874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143598 q = 0) : d144875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143598, d144875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143598, d144875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143599 q = 0) : d144876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143599, d144876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12531 q selected
    | true =>
      simp only [d143599, d144876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12546 q selected
  have h5 (q : Pattern) (selected : d143600 q = 0) : d144877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143600, d144877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143600, d144877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143601 q = 0) : d144878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143601, d144878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143601, d144878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143602 q = 0) : d144879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143602, d144879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143602, d144879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143536 q = 0) : d144813 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143536, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12531 q selected
    | true =>
      simp only [d143536, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12532 q selected
  have h9 (q : Pattern) (selected : d143537 q = 0) : d144814 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143537, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143537, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143538 q = 0) : d144815 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143538, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143538, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143539 q = 0) : d144816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12532 q selected
    | true =>
      simp only [d143539, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143540 q = 0) : d144817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143540, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143541 q = 0) : d144818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143541, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143542 q = 0) : d144819 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143542, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143542, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143603 q = 0) : d144880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143603, d144880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143603, d144880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143604 q = 0) : d144881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143604, d144881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143604, d144881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12548 (p : Pattern) (selected : d143610 p = 0) : d144887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143605 q = 0) : d144882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143605, d144882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12547 q selected
    | true =>
      simp only [d143605, d144882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143606 q = 0) : d144883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143606, d144883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143606, d144883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143607 q = 0) : d144884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143607, d144884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143607, d144884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143608 q = 0) : d144885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143608, d144885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143608, d144885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143609 q = 0) : d144886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143609, d144886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143609, d144886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143610 q = 0) : d144887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143610, d144887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143610, d144887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12549 (p : Pattern) (selected : d1744 p = 0) : d53014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 0) : d53013 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, d53013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1744 q = 0) : d53014 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, d53014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1744, d53014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12550 (p : Pattern) (selected : d1756 p = 0) : d53026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 0) : d53025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, d53025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1756 q = 0) : d53026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, d53026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1756, d53026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12551 (p : Pattern) (selected : d143621 p = 0) : d144822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143612 q = 0) : d144813 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143612, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12549 q selected
    | true =>
      simp only [d143612, d144813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12550 q selected
  have h2 (q : Pattern) (selected : d143613 q = 0) : d144814 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143613, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143613, d144814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143614 q = 0) : d144815 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143614, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143614, d144815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143615 q = 0) : d144816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143615, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12550 q selected
    | true =>
      simp only [d143615, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143616 q = 0) : d144817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143616, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143616, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143617 q = 0) : d144818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143617, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143617, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143618 q = 0) : d144819 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143618, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143618, d144819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143619 q = 0) : d144820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143619, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143619, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143620 q = 0) : d144821 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143620, d144821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143620, d144821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143621 q = 0) : d144822 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143621, d144822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143621, d144822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12552 (p : Pattern) (selected : d143625 p = 0) : d144826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143615 q = 0) : d144816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143615, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12550 q selected
    | true =>
      simp only [d143615, d144816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143616 q = 0) : d144817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143616, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143616, d144817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143617 q = 0) : d144818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143617, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143617, d144818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143619 q = 0) : d144820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143619, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143619, d144820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143624 q = 0) : d144825 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143624, d144825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143624, d144825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143625 q = 0) : d144826 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143625, d144826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143625, d144826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12553 (p : Pattern) (selected : d143631 p = 0) : d144832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143622 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143622, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12551 q selected
    | true =>
      simp only [d143622, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143623 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143623, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143623, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143626 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12552 q selected
    | true =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143627 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143628 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143628, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143628, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143629 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143629, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143629, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143630 q = 0) : d144831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143630, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143630, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143631 q = 0) : d144832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143631, d144832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143631, d144832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12554 (p : Pattern) (selected : d143635 p = 0) : d144836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143626 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12552 q selected
    | true =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143627 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143632 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143632, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143632, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143633 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143633, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143633, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143634 q = 0) : d144835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143634, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143634, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143635 q = 0) : d144836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143635, d144836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143635, d144836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12555 (p : Pattern) (selected : d143641 p = 0) : d144893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143638 q = 0) : d144890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143638, d144890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143638, d144890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143639 q = 0) : d144891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143639, d144891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143639, d144891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143640 q = 0) : d144892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143640, d144892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143640, d144892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143641 q = 0) : d144893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143641, d144893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143641, d144893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12556 (p : Pattern) (selected : d143647 p = 0) : d144899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143583 q = 0) : d144860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143583, d144860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12541 q selected
    | true =>
      simp only [d143583, d144860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12542 q selected
  have h2 (q : Pattern) (selected : d143584 q = 0) : d144861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143584, d144861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143584, d144861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143585 q = 0) : d144862 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143585, d144862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143585, d144862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143586 q = 0) : d144863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143586, d144863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143586, d144863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143593 q = 0) : d144870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143593, d144870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12543 q selected
    | true =>
      simp only [d143593, d144870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12544 q selected
  have h6 (q : Pattern) (selected : d143594 q = 0) : d144871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143594, d144871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143594, d144871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143595 q = 0) : d144872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143595, d144872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143595, d144872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143611 q = 0) : d144888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143611, d144888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12548 q selected
    | true =>
      simp only [d143611, d144888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12535 q selected
  have h9 (q : Pattern) (selected : d143636 q = 0) : d144837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143636, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12553 q selected
    | true =>
      simp only [d143636, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12554 q selected
  have h10 (q : Pattern) (selected : d143637 q = 0) : d144889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143637, d144889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143637, d144889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143642 q = 0) : d144894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143642, d144894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12555 q selected
    | true =>
      simp only [d143642, d144894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143643 q = 0) : d144895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143643, d144895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143643, d144895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143644 q = 0) : d144896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143644, d144896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143644, d144896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143645 q = 0) : d144897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143645, d144897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143645, d144897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143646 q = 0) : d144898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143646, d144898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143646, d144898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143647 q = 0) : d144899 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143647, d144899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143647, d144899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12557 (p : Pattern) (selected : d143648 p = 0) : d144900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143553 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143553, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143579 q = 0) : d144856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143579, d144856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143579, d144856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143648 q = 0) : d144900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143648, d144900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143648, d144900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12558 (p : Pattern) (selected : d143649 p = 0) : d144901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143557 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143557, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143581 q = 0) : d144858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143581, d144858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143581, d144858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143649 q = 0) : d144901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143649, d144901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143649, d144901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12559 (p : Pattern) (selected : d143654 p = 0) : d144906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143552 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143552, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143587 q = 0) : d144864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143587, d144864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143587, d144864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143588 q = 0) : d144865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143588, d144865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143588, d144865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143654 q = 0) : d144906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143654, d144906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143654, d144906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12560 (p : Pattern) (selected : d143655 p = 0) : d144907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143550 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12534 q selected
    | true =>
      simp only [d143550, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143551 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143551, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143556 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143556, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143590 q = 0) : d144867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143590, d144867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143590, d144867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143591 q = 0) : d144868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143591, d144868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143591, d144868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143655 q = 0) : d144907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143655, d144907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143655, d144907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12561 (p : Pattern) (selected : d143659 p = 0) : d144911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143605 q = 0) : d144882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143605, d144882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12547 q selected
    | true =>
      simp only [d143605, d144882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143606 q = 0) : d144883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143606, d144883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143606, d144883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143607 q = 0) : d144884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143607, d144884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143607, d144884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143608 q = 0) : d144885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143608, d144885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143608, d144885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143609 q = 0) : d144886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143609, d144886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143609, d144886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143659 q = 0) : d144911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143659, d144911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143659, d144911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12562 (p : Pattern) (selected : d143661 p = 0) : d144845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143622 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143622, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12551 q selected
    | true =>
      simp only [d143622, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143623 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143623, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143623, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143626 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12552 q selected
    | true =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143627 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143628 q = 0) : d144829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143628, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143628, d144829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143629 q = 0) : d144830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143629, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143629, d144830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143630 q = 0) : d144831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143630, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143630, d144831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143661 q = 0) : d144845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143661, d144845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143661, d144845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12563 (p : Pattern) (selected : d143662 p = 0) : d144846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143626 q = 0) : d144827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12552 q selected
    | true =>
      simp only [d143626, d144827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143627 q = 0) : d144828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, d144828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143632 q = 0) : d144833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143632, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143632, d144833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143633 q = 0) : d144834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143633, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143633, d144834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143634 q = 0) : d144835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143634, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143634, d144835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143662 q = 0) : d144846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143662, d144846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143662, d144846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12564 (p : Pattern) (selected : d143665 p = 0) : d144914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143546 q = 0) : d144823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12533 q selected
    | true =>
      simp only [d143546, d144823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143547 q = 0) : d144824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143547, d144824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143638 q = 0) : d144890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143638, d144890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143638, d144890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143639 q = 0) : d144891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143639, d144891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143639, d144891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143640 q = 0) : d144892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143640, d144892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143640, d144892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143665 q = 0) : d144914 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143665, d144914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143665, d144914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12565 (p : Pattern) (selected : d143671 p = 0) : d144920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143583 q = 0) : d144860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143583, d144860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12541 q selected
    | true =>
      simp only [d143583, d144860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12542 q selected
  have h2 (q : Pattern) (selected : d143584 q = 0) : d144861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143584, d144861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143584, d144861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143585 q = 0) : d144862 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143585, d144862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143585, d144862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143586 q = 0) : d144863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143586, d144863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143586, d144863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143593 q = 0) : d144870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143593, d144870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12543 q selected
    | true =>
      simp only [d143593, d144870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12544 q selected
  have h6 (q : Pattern) (selected : d143594 q = 0) : d144871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143594, d144871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143594, d144871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143595 q = 0) : d144872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143595, d144872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143595, d144872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143611 q = 0) : d144888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143611, d144888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12548 q selected
    | true =>
      simp only [d143611, d144888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12535 q selected
  have h9 (q : Pattern) (selected : d143636 q = 0) : d144837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143636, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12553 q selected
    | true =>
      simp only [d143636, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12554 q selected
  have h10 (q : Pattern) (selected : d143637 q = 0) : d144889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143637, d144889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143637, d144889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143642 q = 0) : d144894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143642, d144894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12555 q selected
    | true =>
      simp only [d143642, d144894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143643 q = 0) : d144895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143643, d144895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143643, d144895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143644 q = 0) : d144896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143644, d144896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143644, d144896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143645 q = 0) : d144897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143645, d144897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143645, d144897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143646 q = 0) : d144898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143646, d144898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143646, d144898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143650 q = 0) : d144902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143650, d144902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12557 q selected
    | true =>
      simp only [d143650, d144902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12558 q selected
  have h17 (q : Pattern) (selected : d143651 q = 0) : d144903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143651, d144903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143651, d144903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143652 q = 0) : d144904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143652, d144904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143652, d144904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d143653 q = 0) : d144905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143653, d144905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143653, d144905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143656 q = 0) : d144908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143656, d144908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12559 q selected
    | true =>
      simp only [d143656, d144908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12560 q selected
  have h21 (q : Pattern) (selected : d143657 q = 0) : d144909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143657, d144909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143657, d144909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d143658 q = 0) : d144910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143658, d144910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143658, d144910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143660 q = 0) : d144912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143660, d144912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12561 q selected
    | true =>
      simp only [d143660, d144912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12538 q selected
  have h24 (q : Pattern) (selected : d143663 q = 0) : d144847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143663, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12562 q selected
    | true =>
      simp only [d143663, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12563 q selected
  have h25 (q : Pattern) (selected : d143664 q = 0) : d144913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143664, d144913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d143664, d144913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d143666 q = 0) : d144915 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143666, d144915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12564 q selected
    | true =>
      simp only [d143666, d144915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d143667 q = 0) : d144916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143667, d144916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d143667, d144916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d143668 q = 0) : d144917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143668, d144917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d143668, d144917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d143669 q = 0) : d144918 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143669, d144918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d143669, d144918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d143670 q = 0) : d144919 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143670, d144919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143670, d144919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d143671 q = 0) : d144920 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143671, d144920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143671, d144920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12566 (p : Pattern) (selected : d143678 p = 0) : d144927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143560 q = 0) : d144837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12535 q selected
    | true =>
      simp only [d143560, d144837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12536 q selected
  have h2 (q : Pattern) (selected : d143561 q = 0) : d144838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143561, d144838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143562 q = 0) : d144839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143562, d144839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143563 q = 0) : d144840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143563, d144840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143564 q = 0) : d144841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143564, d144841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143673 q = 0) : d144922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143673, d144922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12536 q selected
    | true =>
      simp only [d143673, d144922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143674 q = 0) : d144923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143674, d144923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143674, d144923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143675 q = 0) : d144924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143675, d144924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143675, d144924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143676 q = 0) : d144925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143676, d144925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143676, d144925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143677 q = 0) : d144926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143677, d144926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143677, d144926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143678 q = 0) : d144927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143678, d144927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143678, d144927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12567 (p : Pattern) (selected : d143684 p = 0) : d144933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143673 q = 0) : d144922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143673, d144922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12536 q selected
    | true =>
      simp only [d143673, d144922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143674 q = 0) : d144923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143674, d144923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143674, d144923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143675 q = 0) : d144924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143675, d144924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143675, d144924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143676 q = 0) : d144925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143676, d144925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143676, d144925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143677 q = 0) : d144926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143677, d144926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143677, d144926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143679 q = 0) : d144928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143679, d144928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12539 q selected
    | true =>
      simp only [d143679, d144928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143680 q = 0) : d144929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143680, d144929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143680, d144929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143681 q = 0) : d144930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143681, d144930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143681, d144930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143682 q = 0) : d144931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143682, d144931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143682, d144931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143683 q = 0) : d144932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143683, d144932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143683, d144932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143684 q = 0) : d144933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143684, d144933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143684, d144933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12568 (p : Pattern) (selected : d143691 p = 0) : d144940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143660 q = 0) : d144912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143660, d144912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12561 q selected
    | true =>
      simp only [d143660, d144912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12538 q selected
  have h2 (q : Pattern) (selected : d143663 q = 0) : d144847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143663, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12562 q selected
    | true =>
      simp only [d143663, d144847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12563 q selected
  have h3 (q : Pattern) (selected : d143664 q = 0) : d144913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143664, d144913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143664, d144913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143666 q = 0) : d144915 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143666, d144915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12564 q selected
    | true =>
      simp only [d143666, d144915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143667 q = 0) : d144916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143667, d144916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143667, d144916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143668 q = 0) : d144917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143668, d144917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143668, d144917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143689 q = 0) : d144938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143689, d144938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143689, d144938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143690 q = 0) : d144939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143690, d144939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143690, d144939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143691 q = 0) : d144940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143691, d144940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143691, d144940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12569 (p : Pattern) (selected : d143693 p = 0) : d144942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143679 q = 0) : d144928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143679, d144928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12539 q selected
    | true =>
      simp only [d143679, d144928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143680 q = 0) : d144929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143680, d144929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143680, d144929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143681 q = 0) : d144930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143681, d144930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143681, d144930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143682 q = 0) : d144931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143682, d144931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143682, d144931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143683 q = 0) : d144932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143683, d144932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143683, d144932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143693 q = 0) : d144942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143693, d144942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143693, d144942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12570 (p : Pattern) (selected : d1860 p = 0) : d53186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1857 q = 0) : d53183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
  have h2 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1858 q = 0) : d53184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1556 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1859 q = 0) : d53185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1860 q = 0) : d53186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12571 (p : Pattern) (selected : d1865 p = 0) : d53191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1862 q = 0) : d53188 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
  have h2 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1863 q = 0) : d53189 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1571 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1864 q = 0) : d53190 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1865 q = 0) : d53191 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12572 (p : Pattern) (selected : d1871 p = 0) : d53197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1868 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
  have h2 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1870 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1871 q = 0) : d53197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12573 (p : Pattern) (selected : d13493 p = 0) : d113715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13490 q = 0) : d113712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
  have h2 (q : Pattern) (selected : d13351 q = 0) : d113611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8358 q selected
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13491 q = 0) : d113713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13352 q = 0) : d113612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13492 q = 0) : d113714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13493 q = 0) : d113715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12574 (p : Pattern) (selected : d143714 p = 0) : d144963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143699 q = 0) : d144948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143699, d144948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12570 q selected
    | true =>
      simp only [d143699, d144948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12571 q selected
  have h2 (q : Pattern) (selected : d143700 q = 0) : d144949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143700, d144949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143700, d144949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143701 q = 0) : d144950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143701, d144950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143701, d144950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143702 q = 0) : d144951 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143702, d144951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12571 q selected
    | true =>
      simp only [d143702, d144951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12573 q selected
  have h5 (q : Pattern) (selected : d143703 q = 0) : d144952 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143703, d144952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143703, d144952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143704 q = 0) : d144953 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143704, d144953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143704, d144953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143705 q = 0) : d144954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143705, d144954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143705, d144954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143706 q = 0) : d144955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143706, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12571 q selected
    | true =>
      simp only [d143706, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12572 q selected
  have h9 (q : Pattern) (selected : d143707 q = 0) : d144956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143707, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143707, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143708 q = 0) : d144957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143708, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143708, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143709 q = 0) : d144958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12572 q selected
    | true =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143710 q = 0) : d144959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143711 q = 0) : d144960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143712 q = 0) : d144961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143712, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143712, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143713 q = 0) : d144962 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143713, d144962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143713, d144962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143714 q = 0) : d144963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143714, d144963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143714, d144963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12575 (p : Pattern) (selected : d143719 p = 0) : d144968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143706 q = 0) : d144955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143706, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12571 q selected
    | true =>
      simp only [d143706, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12572 q selected
  have h2 (q : Pattern) (selected : d143707 q = 0) : d144956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143707, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143707, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143708 q = 0) : d144957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143708, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143708, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143709 q = 0) : d144958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12572 q selected
    | true =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143710 q = 0) : d144959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143711 q = 0) : d144960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143712 q = 0) : d144961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143712, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143712, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143717 q = 0) : d144966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143717, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143717, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143718 q = 0) : d144967 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143718, d144967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143718, d144967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143719 q = 0) : d144968 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143719, d144968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143719, d144968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12576 (p : Pattern) (selected : d143725 p = 0) : d144974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143715 q = 0) : d144964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143715, d144964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12574 q selected
    | true =>
      simp only [d143715, d144964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143716 q = 0) : d144965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143716, d144965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143716, d144965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143720 q = 0) : d144969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12575 q selected
    | true =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143721 q = 0) : d144970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143722 q = 0) : d144971 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143722, d144971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143722, d144971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143723 q = 0) : d144972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143723, d144972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143723, d144972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143724 q = 0) : d144973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143724, d144973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143724, d144973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143725 q = 0) : d144974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143725, d144974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143725, d144974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12577 (p : Pattern) (selected : d143727 p = 0) : d144976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143709 q = 0) : d144958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12572 q selected
    | true =>
      simp only [d143709, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143710 q = 0) : d144959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143710, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143711 q = 0) : d144960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143711, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143717 q = 0) : d144966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143717, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143717, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143726 q = 0) : d144975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143726, d144975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143726, d144975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143727 q = 0) : d144976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143727, d144976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143727, d144976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12578 (p : Pattern) (selected : d143733 p = 0) : d144982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143720 q = 0) : d144969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12575 q selected
    | true =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143721 q = 0) : d144970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143728 q = 0) : d144977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143728, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12577 q selected
    | true =>
      simp only [d143728, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143729 q = 0) : d144978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143729, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143729, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143730 q = 0) : d144979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143730, d144979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143730, d144979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143731 q = 0) : d144980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143731, d144980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143731, d144980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143732 q = 0) : d144981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143732, d144981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143732, d144981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143733 q = 0) : d144982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143733, d144982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143733, d144982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12579 (p : Pattern) (selected : d1922 p = 0) : d53191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1919 q = 0) : d53188 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d53188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
  have h2 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 0) : d53189 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, d53189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 0) : d53190 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, d53190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1922 q = 0) : d53191 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12580 (p : Pattern) (selected : d1927 p = 0) : d53197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1924 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
  have h2 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1927 q = 0) : d53197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12581 (p : Pattern) (selected : d143744 p = 0) : d144968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143735 q = 0) : d144955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143735, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12579 q selected
    | true =>
      simp only [d143735, d144955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12580 q selected
  have h2 (q : Pattern) (selected : d143736 q = 0) : d144956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143736, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143736, d144956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143737 q = 0) : d144957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143737, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143737, d144957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143738 q = 0) : d144958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143738, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12580 q selected
    | true =>
      simp only [d143738, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143739 q = 0) : d144959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143739, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143739, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143740 q = 0) : d144960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143740, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143740, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143741 q = 0) : d144961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143741, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143741, d144961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143742 q = 0) : d144966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143742, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143742, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143743 q = 0) : d144967 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143743, d144967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143743, d144967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143744 q = 0) : d144968 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143744, d144968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143744, d144968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12582 (p : Pattern) (selected : d143748 p = 0) : d144976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143738 q = 0) : d144958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143738, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12580 q selected
    | true =>
      simp only [d143738, d144958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143739 q = 0) : d144959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143739, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143739, d144959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143740 q = 0) : d144960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143740, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143740, d144960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143742 q = 0) : d144966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143742, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143742, d144966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143747 q = 0) : d144975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143747, d144975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143747, d144975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143748 q = 0) : d144976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143748, d144976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143748, d144976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12583 (p : Pattern) (selected : d143754 p = 0) : d144982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143745 q = 0) : d144969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143745, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12581 q selected
    | true =>
      simp only [d143745, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143746 q = 0) : d144970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143746, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143746, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143749 q = 0) : d144977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143749, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12582 q selected
    | true =>
      simp only [d143749, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143750 q = 0) : d144978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143750, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143750, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143751 q = 0) : d144979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143751, d144979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143751, d144979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143752 q = 0) : d144980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143752, d144980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143752, d144980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143753 q = 0) : d144981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143753, d144981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143753, d144981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143754 q = 0) : d144982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143754, d144982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143754, d144982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12584 (p : Pattern) (selected : d143758 p = 0) : d144987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143749 q = 0) : d144977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143749, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12582 q selected
    | true =>
      simp only [d143749, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143750 q = 0) : d144978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143750, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143750, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143755 q = 0) : d144984 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143755, d144984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143755, d144984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143756 q = 0) : d144985 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143756, d144985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143756, d144985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143757 q = 0) : d144986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143757, d144986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143757, d144986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143758 q = 0) : d144987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143758, d144987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143758, d144987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12585 (p : Pattern) (selected : d143764 p = 0) : d144993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143720 q = 0) : d144969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12575 q selected
    | true =>
      simp only [d143720, d144969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143721 q = 0) : d144970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143721, d144970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143761 q = 0) : d144990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143761, d144990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143761, d144990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143762 q = 0) : d144991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143762, d144991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143762, d144991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143763 q = 0) : d144992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143763, d144992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143763, d144992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143764 q = 0) : d144993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143764, d144993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143764, d144993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12586 (p : Pattern) (selected : d143770 p = 0) : d144999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143734 q = 0) : d144983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143734, d144983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12576 q selected
    | true =>
      simp only [d143734, d144983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12578 q selected
  have h2 (q : Pattern) (selected : d143759 q = 0) : d144988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143759, d144988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12583 q selected
    | true =>
      simp only [d143759, d144988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12584 q selected
  have h3 (q : Pattern) (selected : d143760 q = 0) : d144989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143760, d144989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143760, d144989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143765 q = 0) : d144994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143765, d144994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12585 q selected
    | true =>
      simp only [d143765, d144994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143766 q = 0) : d144995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143766, d144995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143766, d144995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143767 q = 0) : d144996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143767, d144996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143767, d144996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143768 q = 0) : d144997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143768, d144997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143768, d144997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143769 q = 0) : d144998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143769, d144998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143769, d144998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143770 q = 0) : d144999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143770, d144999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143770, d144999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12587 (p : Pattern) (selected : d143775 p = 0) : d144987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143728 q = 0) : d144977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143728, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12577 q selected
    | true =>
      simp only [d143728, d144977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143729 q = 0) : d144978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143729, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143729, d144978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143772 q = 0) : d144984 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143772, d144984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143772, d144984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143773 q = 0) : d144985 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143773, d144985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143773, d144985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143774 q = 0) : d144986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143774, d144986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143774, d144986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143775 q = 0) : d144987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143775, d144987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143775, d144987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12588 (p : Pattern) (selected : d143781 p = 0) : d145006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143776 q = 0) : d145001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143776, d145001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12587 q selected
    | true =>
      simp only [d143776, d145001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143777 q = 0) : d145002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143777, d145002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143777, d145002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143778 q = 0) : d145003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143778, d145003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143778, d145003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143779 q = 0) : d145004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143779, d145004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143779, d145004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143780 q = 0) : d145005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143780, d145005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143780, d145005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143781 q = 0) : d145006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143781, d145006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143781, d145006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12589 (p : Pattern) (selected : d143787 p = 0) : d145012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143566 q = 0) : d144843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143566, d144843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143566, d144843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12537 q selected
  have h2 (q : Pattern) (selected : d143567 q = 0) : d144844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143567, d144844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143567, d144844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d143576 q = 0) : d144853 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143576, d144853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12537 q selected
    | true =>
      simp only [d143576, d144853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12540 q selected
  have h4 (q : Pattern) (selected : d143577 q = 0) : d144854 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143577, d144854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143577, d144854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143578 q = 0) : d144855 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143578, d144855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143578, d144855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143672 q = 0) : d144921 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143672, d144921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12556 q selected
    | true =>
      simp only [d143672, d144921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12565 q selected
  have h7 (q : Pattern) (selected : d143685 q = 0) : d144934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143685, d144934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12566 q selected
    | true =>
      simp only [d143685, d144934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12567 q selected
  have h8 (q : Pattern) (selected : d143686 q = 0) : d144935 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143686, d144935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143686, d144935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143687 q = 0) : d144936 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143687, d144936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143687, d144936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d143688 q = 0) : d144937 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143688, d144937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143688, d144937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143692 q = 0) : d144941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143692, d144941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143692, d144941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12568 q selected
  have h12 (q : Pattern) (selected : d143694 q = 0) : d144943 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143694, d144943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143694, d144943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12569 q selected
  have h13 (q : Pattern) (selected : d143695 q = 0) : d144944 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143695, d144944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143695, d144944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143696 q = 0) : d144945 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143696, d144945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143696, d144945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d143697 q = 0) : d144946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143697, d144946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d143697, d144946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d143698 q = 0) : d144947 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143698, d144947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143698, d144947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143771 q = 0) : d145000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143771, d145000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143771, d145000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12586 q selected
  have h18 (q : Pattern) (selected : d143782 q = 0) : d145007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143782, d145007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143782, d145007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12588 q selected
  have h19 (q : Pattern) (selected : d143783 q = 0) : d145008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143783, d145008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143783, d145008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143784 q = 0) : d145009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143784, d145009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143784, d145009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d143785 q = 0) : d145010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143785, d145010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d143785, d145010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d143786 q = 0) : d145011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143786, d145011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143786, d145011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143787 q = 0) : d145012 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143787, d145012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143787, d145012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro12590 (p : Pattern) (selected : d143793 p = 0) : d145018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143788 q = 0) : d145013 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143788, d145013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143788, d145013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12589 q selected
  have h2 (q : Pattern) (selected : d143789 q = 0) : d145014 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143789, d145014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143789, d145014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143790 q = 0) : d145015 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143790, d145015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143790, d145015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143791 q = 0) : d145016 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143791, d145016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143791, d145016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143792 q = 0) : d145017 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143792, d145017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143792, d145017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143793 q = 0) : d145018 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143793, d145018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143793, d145018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12591 (p : Pattern) (selected : d2056 p = 0) : d53335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2055 q = 0) : d53334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2056 q = 0) : d53335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12592 (p : Pattern) (selected : d2068 p = 0) : d53347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2067 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2068 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12593 (p : Pattern) (selected : d143807 p = 0) : d145032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143798 q = 0) : d145023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143798, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12591 q selected
    | true =>
      simp only [d143798, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12592 q selected
  have h2 (q : Pattern) (selected : d143799 q = 0) : d145024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143799, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143799, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143800 q = 0) : d145025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143800, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143800, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143801 q = 0) : d145026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12592 q selected
    | true =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143802 q = 0) : d145027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143803 q = 0) : d145028 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143804 q = 0) : d145029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143804, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143804, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143805 q = 0) : d145030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143805, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143805, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143806 q = 0) : d145031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143806, d145031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143806, d145031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143807 q = 0) : d145032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143807, d145032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143807, d145032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12594 (p : Pattern) (selected : d143811 p = 0) : d145036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143801 q = 0) : d145026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12592 q selected
    | true =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143802 q = 0) : d145027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143803 q = 0) : d145028 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143805 q = 0) : d145030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143805, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143805, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143810 q = 0) : d145035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143810, d145035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143810, d145035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143811 q = 0) : d145036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143811, d145036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143811, d145036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12595 (p : Pattern) (selected : d143817 p = 0) : d145042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143815 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143816 q = 0) : d145041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143816, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143816, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143817 q = 0) : d145042 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143817, d145042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143817, d145042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12596 (p : Pattern) (selected : d143821 p = 0) : d145046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143819 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143820 q = 0) : d145045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143820, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143820, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143821 q = 0) : d145046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143821, d145046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143821, d145046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12597 (p : Pattern) (selected : d143827 p = 0) : d145052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143822 q = 0) : d145047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12595 q selected
    | true =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12596 q selected
  have h2 (q : Pattern) (selected : d143823 q = 0) : d145048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143824 q = 0) : d145049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143825 q = 0) : d145050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143826 q = 0) : d145051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143827 q = 0) : d145052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143827, d145052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143827, d145052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12598 (p : Pattern) (selected : d143830 p = 0) : d145055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143815 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143816 q = 0) : d145041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143816, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143816, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143830 q = 0) : d145055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143830, d145055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143830, d145055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12599 (p : Pattern) (selected : d143831 p = 0) : d145056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143819 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143820 q = 0) : d145045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143820, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143820, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143831 q = 0) : d145056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143831, d145056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143831, d145056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12600 (p : Pattern) (selected : d143837 p = 0) : d145062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143822 q = 0) : d145047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12595 q selected
    | true =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12596 q selected
  have h2 (q : Pattern) (selected : d143823 q = 0) : d145048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143824 q = 0) : d145049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143825 q = 0) : d145050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143826 q = 0) : d145051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143832 q = 0) : d145057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143832, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12598 q selected
    | true =>
      simp only [d143832, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12599 q selected
  have h7 (q : Pattern) (selected : d143833 q = 0) : d145058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143833, d145058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143833, d145058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143834 q = 0) : d145059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143834, d145059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143834, d145059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143835 q = 0) : d145060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143835, d145060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143835, d145060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143836 q = 0) : d145061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143836, d145061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143836, d145061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143837 q = 0) : d145062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143837, d145062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143837, d145062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12601 (p : Pattern) (selected : d143842 p = 0) : d145067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143815 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143841 q = 0) : d145066 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143841, d145066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143841, d145066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143842 q = 0) : d145067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143842, d145067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143842, d145067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12602 (p : Pattern) (selected : d143844 p = 0) : d145069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143819 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143843 q = 0) : d145068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143843, d145068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143843, d145068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143844 q = 0) : d145069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143844, d145069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143844, d145069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12603 (p : Pattern) (selected : d143851 p = 0) : d145076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143849 q = 0) : d145074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143849, d145074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143849, d145074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143850 q = 0) : d145075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143850, d145075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143850, d145075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143851 q = 0) : d145076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143851, d145076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143851, d145076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12604 (p : Pattern) (selected : d143854 p = 0) : d145079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143852 q = 0) : d145077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143852, d145077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143852, d145077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143853 q = 0) : d145078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143853, d145078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143853, d145078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143854 q = 0) : d145079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143854, d145079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143854, d145079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12605 (p : Pattern) (selected : d2038 p = 0) : d53317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2037 q = 0) : d53316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2038 q = 0) : d53317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12606 (p : Pattern) (selected : d13681 p = 0) : d113871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13678 q = 0) : d113868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13679 q = 0) : d113869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13680 q = 0) : d113870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13681 q = 0) : d113871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12607 (p : Pattern) (selected : d143866 p = 0) : d145091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143858 q = 0) : d145083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143858, d145083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12605 q selected
    | true =>
      simp only [d143858, d145083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12591 q selected
  have h2 (q : Pattern) (selected : d143859 q = 0) : d145084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143859, d145084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143859, d145084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143860 q = 0) : d145085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143860, d145085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143860, d145085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143861 q = 0) : d145086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143861, d145086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12591 q selected
    | true =>
      simp only [d143861, d145086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12606 q selected
  have h5 (q : Pattern) (selected : d143862 q = 0) : d145087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143862, d145087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143862, d145087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143863 q = 0) : d145088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143863, d145088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143863, d145088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143864 q = 0) : d145089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143864, d145089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143864, d145089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143798 q = 0) : d145023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143798, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12591 q selected
    | true =>
      simp only [d143798, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12592 q selected
  have h9 (q : Pattern) (selected : d143799 q = 0) : d145024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143799, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143799, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143800 q = 0) : d145025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143800, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143800, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143801 q = 0) : d145026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12592 q selected
    | true =>
      simp only [d143801, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143802 q = 0) : d145027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143802, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143803 q = 0) : d145028 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143803, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143804 q = 0) : d145029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143804, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143804, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143865 q = 0) : d145090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143865, d145090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143865, d145090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143866 q = 0) : d145091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143866, d145091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143866, d145091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12608 (p : Pattern) (selected : d143872 p = 0) : d145097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143867 q = 0) : d145092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143867, d145092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12607 q selected
    | true =>
      simp only [d143867, d145092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143868 q = 0) : d145093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143868, d145093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143868, d145093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143869 q = 0) : d145094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143869, d145094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143869, d145094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143870 q = 0) : d145095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143870, d145095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143870, d145095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143871 q = 0) : d145096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143871, d145096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143871, d145096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143872 q = 0) : d145097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143872, d145097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143872, d145097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12609 (p : Pattern) (selected : d2222 p = 0) : d53335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 0) : d53334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2222 q = 0) : d53335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12610 (p : Pattern) (selected : d2234 p = 0) : d53347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2234 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12611 (p : Pattern) (selected : d143883 p = 0) : d145032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143874 q = 0) : d145023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143874, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12609 q selected
    | true =>
      simp only [d143874, d145023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12610 q selected
  have h2 (q : Pattern) (selected : d143875 q = 0) : d145024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143875, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143875, d145024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143876 q = 0) : d145025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143876, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143876, d145025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143877 q = 0) : d145026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143877, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12610 q selected
    | true =>
      simp only [d143877, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143878 q = 0) : d145027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143878, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143878, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143879 q = 0) : d145028 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143879, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143879, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143880 q = 0) : d145029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143880, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143880, d145029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143881 q = 0) : d145030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143881, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143881, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143882 q = 0) : d145031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143882, d145031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143882, d145031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143883 q = 0) : d145032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143883, d145032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143883, d145032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12612 (p : Pattern) (selected : d143887 p = 0) : d145036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143877 q = 0) : d145026 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143877, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12610 q selected
    | true =>
      simp only [d143877, d145026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143878 q = 0) : d145027 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143878, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143878, d145027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143879 q = 0) : d145028 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143879, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143879, d145028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143881 q = 0) : d145030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143881, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143881, d145030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143886 q = 0) : d145035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143886, d145035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143886, d145035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143887 q = 0) : d145036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143887, d145036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143887, d145036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12613 (p : Pattern) (selected : d143893 p = 0) : d145042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143884 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143884, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12611 q selected
    | true =>
      simp only [d143884, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143885 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143885, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143885, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143888 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12612 q selected
    | true =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143889 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143890 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143890, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143890, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143891 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143891, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143891, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143892 q = 0) : d145041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143892, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143892, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143893 q = 0) : d145042 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143893, d145042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143893, d145042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12614 (p : Pattern) (selected : d143897 p = 0) : d145046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143888 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12612 q selected
    | true =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143889 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143894 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143894, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143894, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143895 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143895, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143895, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143896 q = 0) : d145045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143896, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143896, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143897 q = 0) : d145046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143897, d145046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143897, d145046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12615 (p : Pattern) (selected : d143903 p = 0) : d145103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143900 q = 0) : d145100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143900, d145100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143900, d145100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143901 q = 0) : d145101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143901, d145101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143901, d145101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143902 q = 0) : d145102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143902, d145102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143902, d145102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143903 q = 0) : d145103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143903, d145103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143903, d145103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12616 (p : Pattern) (selected : d143909 p = 0) : d145109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143845 q = 0) : d145070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143845, d145070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12601 q selected
    | true =>
      simp only [d143845, d145070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12602 q selected
  have h2 (q : Pattern) (selected : d143846 q = 0) : d145071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143846, d145071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143846, d145071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143847 q = 0) : d145072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143847, d145072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143847, d145072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143848 q = 0) : d145073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143848, d145073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143848, d145073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143855 q = 0) : d145080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143855, d145080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12603 q selected
    | true =>
      simp only [d143855, d145080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12604 q selected
  have h6 (q : Pattern) (selected : d143856 q = 0) : d145081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143856, d145081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143856, d145081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143857 q = 0) : d145082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143857, d145082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143857, d145082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143873 q = 0) : d145098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143873, d145098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12608 q selected
    | true =>
      simp only [d143873, d145098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12595 q selected
  have h9 (q : Pattern) (selected : d143898 q = 0) : d145047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143898, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12613 q selected
    | true =>
      simp only [d143898, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12614 q selected
  have h10 (q : Pattern) (selected : d143899 q = 0) : d145099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143899, d145099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143899, d145099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143904 q = 0) : d145104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143904, d145104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12615 q selected
    | true =>
      simp only [d143904, d145104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143905 q = 0) : d145105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143905, d145105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143905, d145105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143906 q = 0) : d145106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143906, d145106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143906, d145106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143907 q = 0) : d145107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143907, d145107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143907, d145107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143908 q = 0) : d145108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143908, d145108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143908, d145108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143909 q = 0) : d145109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143909, d145109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143909, d145109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro12617 (p : Pattern) (selected : d143910 p = 0) : d145110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143815 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143815, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143841 q = 0) : d145066 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143841, d145066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143841, d145066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143910 q = 0) : d145110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143910, d145110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143910, d145110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12618 (p : Pattern) (selected : d143911 p = 0) : d145111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143819 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143819, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143843 q = 0) : d145068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143843, d145068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143843, d145068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143911 q = 0) : d145111 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143911, d145111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143911, d145111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12619 (p : Pattern) (selected : d143916 p = 0) : d145116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143814 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143814, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143849 q = 0) : d145074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143849, d145074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143849, d145074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143850 q = 0) : d145075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143850, d145075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143850, d145075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143916 q = 0) : d145116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143916, d145116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143916, d145116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12620 (p : Pattern) (selected : d143917 p = 0) : d145117 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143812 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12594 q selected
    | true =>
      simp only [d143812, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143813 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143813, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143818 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143818, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143852 q = 0) : d145077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143852, d145077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143852, d145077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143853 q = 0) : d145078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143853, d145078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143853, d145078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143917 q = 0) : d145117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143917, d145117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143917, d145117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12621 (p : Pattern) (selected : d143921 p = 0) : d145121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143867 q = 0) : d145092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143867, d145092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12607 q selected
    | true =>
      simp only [d143867, d145092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143868 q = 0) : d145093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143868, d145093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143868, d145093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143869 q = 0) : d145094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143869, d145094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143869, d145094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143870 q = 0) : d145095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143870, d145095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143870, d145095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143871 q = 0) : d145096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143871, d145096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143871, d145096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143921 q = 0) : d145121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143921, d145121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143921, d145121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12622 (p : Pattern) (selected : d143923 p = 0) : d145055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143884 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143884, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12611 q selected
    | true =>
      simp only [d143884, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143885 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143885, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143885, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143888 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12612 q selected
    | true =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143889 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143890 q = 0) : d145039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143890, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143890, d145039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143891 q = 0) : d145040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143891, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143891, d145040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143892 q = 0) : d145041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143892, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143892, d145041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143923 q = 0) : d145055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143923, d145055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143923, d145055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12623 (p : Pattern) (selected : d143924 p = 0) : d145056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143888 q = 0) : d145037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12612 q selected
    | true =>
      simp only [d143888, d145037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143889 q = 0) : d145038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143889, d145038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143894 q = 0) : d145043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143894, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143894, d145043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143895 q = 0) : d145044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143895, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143895, d145044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143896 q = 0) : d145045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143896, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143896, d145045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143924 q = 0) : d145056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143924, d145056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143924, d145056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12624 (p : Pattern) (selected : d143927 p = 0) : d145124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143808 q = 0) : d145033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12593 q selected
    | true =>
      simp only [d143808, d145033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143809 q = 0) : d145034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143809, d145034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143900 q = 0) : d145100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143900, d145100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143900, d145100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143901 q = 0) : d145101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143901, d145101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143901, d145101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143902 q = 0) : d145102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143902, d145102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143902, d145102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143927 q = 0) : d145124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143927, d145124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143927, d145124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12625 (p : Pattern) (selected : d143933 p = 0) : d145130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143845 q = 0) : d145070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143845, d145070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12601 q selected
    | true =>
      simp only [d143845, d145070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12602 q selected
  have h2 (q : Pattern) (selected : d143846 q = 0) : d145071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143846, d145071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143846, d145071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143847 q = 0) : d145072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143847, d145072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143847, d145072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143848 q = 0) : d145073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143848, d145073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143848, d145073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143855 q = 0) : d145080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143855, d145080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12603 q selected
    | true =>
      simp only [d143855, d145080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12604 q selected
  have h6 (q : Pattern) (selected : d143856 q = 0) : d145081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143856, d145081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143856, d145081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143857 q = 0) : d145082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143857, d145082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143857, d145082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143873 q = 0) : d145098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143873, d145098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12608 q selected
    | true =>
      simp only [d143873, d145098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12595 q selected
  have h9 (q : Pattern) (selected : d143898 q = 0) : d145047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143898, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12613 q selected
    | true =>
      simp only [d143898, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12614 q selected
  have h10 (q : Pattern) (selected : d143899 q = 0) : d145099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143899, d145099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143899, d145099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143904 q = 0) : d145104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143904, d145104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12615 q selected
    | true =>
      simp only [d143904, d145104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143905 q = 0) : d145105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143905, d145105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143905, d145105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d143906 q = 0) : d145106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143906, d145106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143906, d145106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143907 q = 0) : d145107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143907, d145107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143907, d145107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143908 q = 0) : d145108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143908, d145108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143908, d145108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143912 q = 0) : d145112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143912, d145112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12617 q selected
    | true =>
      simp only [d143912, d145112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12618 q selected
  have h17 (q : Pattern) (selected : d143913 q = 0) : d145113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143913, d145113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143913, d145113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143914 q = 0) : d145114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143914, d145114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143914, d145114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d143915 q = 0) : d145115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143915, d145115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143915, d145115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d143918 q = 0) : d145118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143918, d145118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12619 q selected
    | true =>
      simp only [d143918, d145118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12620 q selected
  have h21 (q : Pattern) (selected : d143919 q = 0) : d145119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143919, d145119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143919, d145119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d143920 q = 0) : d145120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143920, d145120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d143920, d145120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d143922 q = 0) : d145122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143922, d145122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12621 q selected
    | true =>
      simp only [d143922, d145122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12598 q selected
  have h24 (q : Pattern) (selected : d143925 q = 0) : d145057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143925, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12622 q selected
    | true =>
      simp only [d143925, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12623 q selected
  have h25 (q : Pattern) (selected : d143926 q = 0) : d145123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143926, d145123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d143926, d145123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d143928 q = 0) : d145125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143928, d145125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12624 q selected
    | true =>
      simp only [d143928, d145125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d143929 q = 0) : d145126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143929, d145126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d143929, d145126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d143930 q = 0) : d145127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143930, d145127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d143930, d145127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d143931 q = 0) : d145128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143931, d145128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d143931, d145128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d143932 q = 0) : d145129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143932, d145129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d143932, d145129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d143933 q = 0) : d145130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143933, d145130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143933, d145130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro12626 (p : Pattern) (selected : d143940 p = 0) : d145137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143822 q = 0) : d145047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12595 q selected
    | true =>
      simp only [d143822, d145047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12596 q selected
  have h2 (q : Pattern) (selected : d143823 q = 0) : d145048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143823, d145048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143824 q = 0) : d145049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143824, d145049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143825 q = 0) : d145050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143825, d145050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143826 q = 0) : d145051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143826, d145051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143935 q = 0) : d145132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143935, d145132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12596 q selected
    | true =>
      simp only [d143935, d145132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143936 q = 0) : d145133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143936, d145133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143936, d145133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143937 q = 0) : d145134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143937, d145134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143937, d145134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143938 q = 0) : d145135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143938, d145135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143938, d145135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143939 q = 0) : d145136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143939, d145136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143939, d145136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143940 q = 0) : d145137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143940, d145137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143940, d145137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12627 (p : Pattern) (selected : d143946 p = 0) : d145143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143935 q = 0) : d145132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143935, d145132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12596 q selected
    | true =>
      simp only [d143935, d145132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143936 q = 0) : d145133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143936, d145133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143936, d145133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143937 q = 0) : d145134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143937, d145134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143937, d145134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143938 q = 0) : d145135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143938, d145135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143938, d145135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143939 q = 0) : d145136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143939, d145136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143939, d145136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143941 q = 0) : d145138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143941, d145138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12599 q selected
    | true =>
      simp only [d143941, d145138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143942 q = 0) : d145139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143942, d145139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143942, d145139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143943 q = 0) : d145140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143943, d145140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143943, d145140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143944 q = 0) : d145141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143944, d145141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143944, d145141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143945 q = 0) : d145142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143945, d145142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143945, d145142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143946 q = 0) : d145143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143946, d145143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143946, d145143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro12628 (p : Pattern) (selected : d143953 p = 0) : d145150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143922 q = 0) : d145122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143922, d145122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12621 q selected
    | true =>
      simp only [d143922, d145122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12598 q selected
  have h2 (q : Pattern) (selected : d143925 q = 0) : d145057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143925, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12622 q selected
    | true =>
      simp only [d143925, d145057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12623 q selected
  have h3 (q : Pattern) (selected : d143926 q = 0) : d145123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143926, d145123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143926, d145123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143928 q = 0) : d145125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143928, d145125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12624 q selected
    | true =>
      simp only [d143928, d145125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143929 q = 0) : d145126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143929, d145126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143929, d145126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143930 q = 0) : d145127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143930, d145127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143930, d145127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143951 q = 0) : d145148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143951, d145148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143951, d145148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143952 q = 0) : d145149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143952, d145149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143952, d145149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143953 q = 0) : d145150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143953, d145150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143953, d145150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12629 (p : Pattern) (selected : d143955 p = 0) : d145152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143941 q = 0) : d145138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143941, d145138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12599 q selected
    | true =>
      simp only [d143941, d145138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143942 q = 0) : d145139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143942, d145139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143942, d145139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143943 q = 0) : d145140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143943, d145140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143943, d145140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143944 q = 0) : d145141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143944, d145141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143944, d145141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143945 q = 0) : d145142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143945, d145142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143945, d145142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143955 q = 0) : d145152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143955, d145152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143955, d145152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12630 (p : Pattern) (selected : d2338 p = 0) : d53503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2335 q = 0) : d53500 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
  have h2 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 0) : d53501 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2337 q = 0) : d53502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2338 q = 0) : d53503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12631 (p : Pattern) (selected : d2343 p = 0) : d53508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2340 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
  have h2 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2341 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2342 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2343 q = 0) : d53508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12632 (p : Pattern) (selected : d2349 p = 0) : d53514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2346 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2349 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12633 (p : Pattern) (selected : d13820 p = 0) : d113972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13817 q = 0) : d113969 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
  have h2 (q : Pattern) (selected : d13678 q = 0) : d113868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8427 q selected
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13818 q = 0) : d113970 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13679 q = 0) : d113869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13819 q = 0) : d113971 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13820 q = 0) : d113972 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12634 (p : Pattern) (selected : d143976 p = 0) : d145173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143961 q = 0) : d145158 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143961, d145158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12630 q selected
    | true =>
      simp only [d143961, d145158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12631 q selected
  have h2 (q : Pattern) (selected : d143962 q = 0) : d145159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143962, d145159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143962, d145159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143963 q = 0) : d145160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143963, d145160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143963, d145160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143964 q = 0) : d145161 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143964, d145161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12631 q selected
    | true =>
      simp only [d143964, d145161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12633 q selected
  have h5 (q : Pattern) (selected : d143965 q = 0) : d145162 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143965, d145162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143965, d145162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143966 q = 0) : d145163 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143966, d145163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143966, d145163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143967 q = 0) : d145164 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143967, d145164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143967, d145164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143968 q = 0) : d145165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143968, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12631 q selected
    | true =>
      simp only [d143968, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12632 q selected
  have h9 (q : Pattern) (selected : d143969 q = 0) : d145166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143969, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143969, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143970 q = 0) : d145167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143970, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143970, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143971 q = 0) : d145168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12632 q selected
    | true =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d143972 q = 0) : d145169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143973 q = 0) : d145170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143974 q = 0) : d145171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143974, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143974, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d143975 q = 0) : d145172 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143975, d145172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143975, d145172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143976 q = 0) : d145173 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143976, d145173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143976, d145173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro12635 (p : Pattern) (selected : d143981 p = 0) : d145178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143968 q = 0) : d145165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143968, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12631 q selected
    | true =>
      simp only [d143968, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12632 q selected
  have h2 (q : Pattern) (selected : d143969 q = 0) : d145166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143969, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143969, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143970 q = 0) : d145167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143970, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143970, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143971 q = 0) : d145168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12632 q selected
    | true =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143972 q = 0) : d145169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143973 q = 0) : d145170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143974 q = 0) : d145171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143974, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143974, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143979 q = 0) : d145176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143979, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143979, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143980 q = 0) : d145177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143980, d145177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143980, d145177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143981 q = 0) : d145178 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143981, d145178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143981, d145178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12636 (p : Pattern) (selected : d143987 p = 0) : d145184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143977 q = 0) : d145174 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143977, d145174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12634 q selected
    | true =>
      simp only [d143977, d145174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143978 q = 0) : d145175 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143978, d145175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143978, d145175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143982 q = 0) : d145179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12635 q selected
    | true =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143983 q = 0) : d145180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143984 q = 0) : d145181 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143984, d145181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143984, d145181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143985 q = 0) : d145182 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143985, d145182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143985, d145182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143986 q = 0) : d145183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143986, d145183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143986, d145183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143987 q = 0) : d145184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143987, d145184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143987, d145184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12637 (p : Pattern) (selected : d143989 p = 0) : d145186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143971 q = 0) : d145168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12632 q selected
    | true =>
      simp only [d143971, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143972 q = 0) : d145169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143972, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143973 q = 0) : d145170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143973, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143979 q = 0) : d145176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143979, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143979, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143988 q = 0) : d145185 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143988, d145185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143988, d145185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143989 q = 0) : d145186 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143989, d145186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143989, d145186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12638 (p : Pattern) (selected : d143995 p = 0) : d145192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143982 q = 0) : d145179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12635 q selected
    | true =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143983 q = 0) : d145180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143990 q = 0) : d145187 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143990, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12637 q selected
    | true =>
      simp only [d143990, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143991 q = 0) : d145188 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143991, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143991, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143992 q = 0) : d145189 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143992, d145189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143992, d145189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143993 q = 0) : d145190 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143993, d145190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143993, d145190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143994 q = 0) : d145191 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143994, d145191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143994, d145191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143995 q = 0) : d145192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143995, d145192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143995, d145192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12639 (p : Pattern) (selected : d2400 p = 0) : d53508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2397 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
  have h2 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2400 q = 0) : d53508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2400, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12640 (p : Pattern) (selected : d2405 p = 0) : d53514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2402 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
  have h2 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2405 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12641 (p : Pattern) (selected : d144006 p = 0) : d145178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143997 q = 0) : d145165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143997, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12639 q selected
    | true =>
      simp only [d143997, d145165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12640 q selected
  have h2 (q : Pattern) (selected : d143998 q = 0) : d145166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143998, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143998, d145166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143999 q = 0) : d145167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143999, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143999, d145167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d144000 q = 0) : d145168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144000, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12640 q selected
    | true =>
      simp only [d144000, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144001 q = 0) : d145169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144001, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144001, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d144002 q = 0) : d145170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144002, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144002, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d144003 q = 0) : d145171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144003, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144003, d145171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d144004 q = 0) : d145176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144004, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d144004, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d144005 q = 0) : d145177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144005, d145177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d144005, d145177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d144006 q = 0) : d145178 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144006, d145178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d144006, d145178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12642 (p : Pattern) (selected : d144010 p = 0) : d145186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144000 q = 0) : d145168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144000, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12640 q selected
    | true =>
      simp only [d144000, d145168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144001 q = 0) : d145169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144001, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144001, d145169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144002 q = 0) : d145170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144002, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144002, d145170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d144004 q = 0) : d145176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144004, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144004, d145176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144009 q = 0) : d145185 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144009, d145185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144009, d145185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144010 q = 0) : d145186 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144010, d145186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144010, d145186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12643 (p : Pattern) (selected : d144016 p = 0) : d145192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144007 q = 0) : d145179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144007, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12641 q selected
    | true =>
      simp only [d144007, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144008 q = 0) : d145180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144008, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144008, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144011 q = 0) : d145187 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144011, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12642 q selected
    | true =>
      simp only [d144011, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144012 q = 0) : d145188 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144012, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144012, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d144013 q = 0) : d145189 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144013, d145189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144013, d145189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d144014 q = 0) : d145190 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144014, d145190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144014, d145190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d144015 q = 0) : d145191 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144015, d145191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d144015, d145191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d144016 q = 0) : d145192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144016, d145192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d144016, d145192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12644 (p : Pattern) (selected : d144020 p = 0) : d145197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144011 q = 0) : d145187 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144011, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12642 q selected
    | true =>
      simp only [d144011, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144012 q = 0) : d145188 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144012, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144012, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144017 q = 0) : d145194 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144017, d145194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144017, d145194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144018 q = 0) : d145195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144018, d145195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144018, d145195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144019 q = 0) : d145196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144019, d145196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144019, d145196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144020 q = 0) : d145197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144020, d145197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144020, d145197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12645 (p : Pattern) (selected : d144026 p = 0) : d145203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143982 q = 0) : d145179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12635 q selected
    | true =>
      simp only [d143982, d145179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143983 q = 0) : d145180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143983, d145180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144023 q = 0) : d145200 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144023, d145200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144023, d145200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144024 q = 0) : d145201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144024, d145201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144024, d145201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144025 q = 0) : d145202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144025, d145202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144025, d145202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144026 q = 0) : d145203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144026, d145203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144026, d145203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12646 (p : Pattern) (selected : d144032 p = 0) : d145209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143996 q = 0) : d145193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143996, d145193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12636 q selected
    | true =>
      simp only [d143996, d145193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12638 q selected
  have h2 (q : Pattern) (selected : d144021 q = 0) : d145198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144021, d145198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12643 q selected
    | true =>
      simp only [d144021, d145198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12644 q selected
  have h3 (q : Pattern) (selected : d144022 q = 0) : d145199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144022, d145199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144022, d145199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d144027 q = 0) : d145204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144027, d145204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12645 q selected
    | true =>
      simp only [d144027, d145204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144028 q = 0) : d145205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144028, d145205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144028, d145205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144029 q = 0) : d145206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144029, d145206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144029, d145206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d144030 q = 0) : d145207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144030, d145207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144030, d145207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d144031 q = 0) : d145208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144031, d145208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144031, d145208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d144032 q = 0) : d145209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144032, d145209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144032, d145209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro12647 (p : Pattern) (selected : d144037 p = 0) : d145197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143990 q = 0) : d145187 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143990, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12637 q selected
    | true =>
      simp only [d143990, d145187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143991 q = 0) : d145188 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143991, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143991, d145188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144034 q = 0) : d145194 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144034, d145194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144034, d145194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144035 q = 0) : d145195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144035, d145195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144035, d145195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144036 q = 0) : d145196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144036, d145196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144036, d145196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144037 q = 0) : d145197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144037, d145197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144037, d145197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12648 (p : Pattern) (selected : d144043 p = 0) : d145216 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144038 q = 0) : d145211 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144038, d145211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12647 q selected
    | true =>
      simp only [d144038, d145211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144039 q = 0) : d145212 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144039, d145212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144039, d145212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144040 q = 0) : d145213 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144040, d145213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144040, d145213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144041 q = 0) : d145214 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144041, d145214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144041, d145214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d144042 q = 0) : d145215 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144042, d145215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144042, d145215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d144043 q = 0) : d145216 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144043, d145216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144043, d145216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12649 (p : Pattern) (selected : d144049 p = 0) : d145222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d143828 q = 0) : d145053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143828, d145053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143828, d145053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12597 q selected
  have h2 (q : Pattern) (selected : d143829 q = 0) : d145054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143829, d145054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143829, d145054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d143838 q = 0) : d145063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143838, d145063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12597 q selected
    | true =>
      simp only [d143838, d145063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12600 q selected
  have h4 (q : Pattern) (selected : d143839 q = 0) : d145064 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143839, d145064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143839, d145064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143840 q = 0) : d145065 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143840, d145065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143840, d145065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143934 q = 0) : d145131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143934, d145131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12616 q selected
    | true =>
      simp only [d143934, d145131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12625 q selected
  have h7 (q : Pattern) (selected : d143947 q = 0) : d145144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143947, d145144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12626 q selected
    | true =>
      simp only [d143947, d145144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12627 q selected
  have h8 (q : Pattern) (selected : d143948 q = 0) : d145145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143948, d145145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143948, d145145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143949 q = 0) : d145146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143949, d145146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143949, d145146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d143950 q = 0) : d145147 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143950, d145147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143950, d145147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d143954 q = 0) : d145151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143954, d145151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143954, d145151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12628 q selected
  have h12 (q : Pattern) (selected : d143956 q = 0) : d145153 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143956, d145153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143956, d145153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12629 q selected
  have h13 (q : Pattern) (selected : d143957 q = 0) : d145154 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143957, d145154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143957, d145154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143958 q = 0) : d145155 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143958, d145155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143958, d145155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d143959 q = 0) : d145156 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143959, d145156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d143959, d145156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d143960 q = 0) : d145157 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143960, d145157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143960, d145157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d144033 q = 0) : d145210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144033, d145210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144033, d145210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12646 q selected
  have h18 (q : Pattern) (selected : d144044 q = 0) : d145217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144044, d145217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144044, d145217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12648 q selected
  have h19 (q : Pattern) (selected : d144045 q = 0) : d145218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144045, d145218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d144045, d145218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d144046 q = 0) : d145219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144046, d145219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d144046, d145219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d144047 q = 0) : d145220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144047, d145220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d144047, d145220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d144048 q = 0) : d145221 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144048, d145221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d144048, d145221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d144049 q = 0) : d145222 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144049, d145222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d144049, d145222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro12650 (p : Pattern) (selected : d144055 p = 0) : d145228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144050 q = 0) : d145223 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144050, d145223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144050, d145223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12649 q selected
  have h2 (q : Pattern) (selected : d144051 q = 0) : d145224 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144051, d145224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144051, d145224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d144052 q = 0) : d145225 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144052, d145225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144052, d145225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d144053 q = 0) : d145226 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144053, d145226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144053, d145226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d144054 q = 0) : d145227 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144054, d145227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144054, d145227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d144055 q = 0) : d145228 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144055, d145228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d144055, d145228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12651 (p : Pattern) (selected : d144061 p = 0) : d145234 p = 1 := by
  have h0 (q : Pattern) (selected : d143020 q = 0) : d144401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d143020, d144401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12382 q selected
    | true =>
      simp only [d143020, d144401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d143273 q = 0) : d144602 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d143273, d144602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143273, d144602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12470 q selected
  have h3 (q : Pattern) (selected : d143274 q = 0) : d144603 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d143274, d144603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143274, d144603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143533 q = 0) : d144810 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d143533, d144810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143533, d144810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12530 q selected
  have h5 (q : Pattern) (selected : d143534 q = 0) : d144811 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d143534, d144811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143534, d144811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143535 q = 0) : d144812 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d143535, d144812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143535, d144812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143794 q = 0) : d145019 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d143794, d145019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143794, d145019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12590 q selected
  have h8 (q : Pattern) (selected : d143795 q = 0) : d145020 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d143795, d145020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143795, d145020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143796 q = 0) : d145021 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d143796, d145021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143796, d145021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143797 q = 0) : d145022 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d143797, d145022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143797, d145022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d144056 q = 0) : d145229 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144056, d145229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144056, d145229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12650 q selected
  have h12 (q : Pattern) (selected : d144057 q = 0) : d145230 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d144057, d145230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144057, d145230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d144058 q = 0) : d145231 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d144058, d145231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144058, d145231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d144059 q = 0) : d145232 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d144059, d145232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144059, d145232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d144060 q = 0) : d145233 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d144060, d145233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d144060, d145233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d144061 q = 0) : d145234 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d144061, d145234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d144061, d145234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro12652 (p : Pattern) (selected : d144067 p = 0) : d145240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144062 q = 0) : d145235 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d144062, d145235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12651 q selected
    | true =>
      simp only [d144062, d145235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144063 q = 0) : d145236 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d144063, d145236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144063, d145236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144064 q = 0) : d145237 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d144064, d145237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144064, d145237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144065 q = 0) : d145238 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d144065, d145238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144065, d145238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144066 q = 0) : d145239 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d144066, d145239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144066, d145239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144067 q = 0) : d145240 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d144067, d145240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144067, d145240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12653 (p : Pattern) (selected : d144073 p = 0) : d145246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144068 q = 0) : d145241 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d144068, d145241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12652 q selected
    | true =>
      simp only [d144068, d145241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144069 q = 0) : d145242 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d144069, d145242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144069, d145242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144070 q = 0) : d145243 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d144070, d145243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144070, d145243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144071 q = 0) : d145244 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d144071, d145244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144071, d145244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144072 q = 0) : d145245 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d144072, d145245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144072, d145245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144073 q = 0) : d145246 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d144073, d145246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144073, d145246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12654 (p : Pattern) (selected : d144079 p = 0) : d145252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144074 q = 0) : d145247 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d144074, d145247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12653 q selected
    | true =>
      simp only [d144074, d145247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144075 q = 0) : d145248 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d144075, d145248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144075, d145248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144076 q = 0) : d145249 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d144076, d145249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144076, d145249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144077 q = 0) : d145250 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d144077, d145250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144077, d145250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144078 q = 0) : d145251 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d144078, d145251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144078, d145251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144079 q = 0) : d145252 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d144079, d145252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144079, d145252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12655 (p : Pattern) (selected : d144085 p = 0) : d145258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144080 q = 0) : d145253 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d144080, d145253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12654 q selected
    | true =>
      simp only [d144080, d145253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144081 q = 0) : d145254 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d144081, d145254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144081, d145254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144082 q = 0) : d145255 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d144082, d145255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144082, d145255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144083 q = 0) : d145256 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d144083, d145256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144083, d145256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144084 q = 0) : d145257 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d144084, d145257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144084, d145257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144085 q = 0) : d145258 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d144085, d145258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144085, d145258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12656 (p : Pattern) (selected : d144091 p = 0) : d145264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144086 q = 0) : d145259 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d144086, d145259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12655 q selected
    | true =>
      simp only [d144086, d145259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144087 q = 0) : d145260 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d144087, d145260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144087, d145260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144088 q = 0) : d145261 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d144088, d145261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144088, d145261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144089 q = 0) : d145262 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d144089, d145262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144089, d145262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144090 q = 0) : d145263 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d144090, d145263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144090, d145263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144091 q = 0) : d145264 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d144091, d145264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144091, d145264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12657 (p : Pattern) (selected : d144097 p = 0) : d145270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144092 q = 0) : d145265 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d144092, d145265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12656 q selected
    | true =>
      simp only [d144092, d145265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144093 q = 0) : d145266 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d144093, d145266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144093, d145266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144094 q = 0) : d145267 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d144094, d145267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144094, d145267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144095 q = 0) : d145268 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d144095, d145268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144095, d145268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144096 q = 0) : d145269 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d144096, d145269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144096, d145269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144097 q = 0) : d145270 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d144097, d145270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144097, d145270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12658 (p : Pattern) (selected : d144103 p = 0) : d145276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d144098 q = 0) : d145271 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d144098, d145271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12657 q selected
    | true =>
      simp only [d144098, d145271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d144099 q = 0) : d145272 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d144099, d145272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d144099, d145272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d144100 q = 0) : d145273 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d144100, d145273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d144100, d145273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d144101 q = 0) : d145274 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d144101, d145274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d144101, d145274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d144102 q = 0) : d145275 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d144102, d145275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d144102, d145275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d144103 q = 0) : d145276 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d144103, d145276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d144103, d145276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12659 (p : Pattern) (selected : d173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12660 (p : Pattern) (selected : d142776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12659 q selected
    | true =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142775 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142776 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12661 (p : Pattern) (selected : d142782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12662 (p : Pattern) (selected : d142788 p = 1) : d146547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142751 q = 1) : d142751 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142757 q = 1) : d142757 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d142770 q = 1) : d142770 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d142783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
    | true =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142784 q = 1) : d146543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142784, d146543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142784, d146543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142680 q = 1) : d142680 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d142785 q = 1) : d146544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142785, d146544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142785, d146544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142786 q = 1) : d146545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142786, d146545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142786, d146545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142787 q = 1) : d146546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142787, d146546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142787, d146546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142788 q = 1) : d146547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142788, d146547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142788, d146547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro12663 (p : Pattern) (selected : d142800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12664 (p : Pattern) (selected : d142806 p = 1) : d146552 p = 1 := by
  have h0 (q : Pattern) (selected : d142751 q = 1) : d142751 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142757 q = 1) : d142757 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142770 q = 1) : d142770 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d142783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
    | true =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142784 q = 1) : d146543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142784, d146543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142784, d146543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142680 q = 1) : d142680 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d142785 q = 1) : d146544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142785, d146544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142785, d146544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142786 q = 1) : d146545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142786, d146545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142786, d146545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142787 q = 1) : d146546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142787, d146546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142787, d146546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142793 q = 1) : d142793 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d142797 q = 1) : d142797 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d142799 q = 1) : d142799 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d142801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
    | true =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d142802 q = 1) : d146548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142802, d146548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142802, d146548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142687 q = 1) : d142687 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d142803 q = 1) : d146549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142803, d146549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d142803, d146549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d142804 q = 1) : d146550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142804, d146550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142804, d146550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d142805 q = 1) : d146551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142805, d146551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142805, d146551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d142806 q = 1) : d146552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142806, d146552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142806, d146552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro12665 (p : Pattern) (selected : d142815 p = 1) : d146559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142799 q = 1) : d142799 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
    | true =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142802 q = 1) : d146548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142802, d146548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142802, d146548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142687 q = 1) : d142687 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142803 q = 1) : d146549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142803, d146549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142803, d146549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142813 q = 1) : d146557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142813, d146557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142813, d146557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142814 q = 1) : d146558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142814, d146558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142814, d146558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142815 q = 1) : d146559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142815, d146559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142815, d146559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12666 (p : Pattern) (selected : d248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h2 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12667 (p : Pattern) (selected : d142839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142834 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12666 q selected
    | true =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142835 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142836 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142837 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142838 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142839 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12668 (p : Pattern) (selected : d142845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142840 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12667 q selected
    | true =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142841 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142842 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142843 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142845 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12669 (p : Pattern) (selected : d142851 p = 1) : d146569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142833 q = 1) : d142833 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12668 q selected
    | true =>
      simp only [d142846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142847 q = 1) : d146565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142847, d146565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142847, d146565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142715 q = 1) : d142715 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142848 q = 1) : d146566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142848, d146566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142848, d146566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142849 q = 1) : d146567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142849, d146567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142849, d146567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142850 q = 1) : d146568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142850, d146568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142850, d146568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142851 q = 1) : d146569 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142851, d146569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142851, d146569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12670 (p : Pattern) (selected : d142857 p = 1) : d146575 p = 1 := by
  have h0 (q : Pattern) (selected : d142745 q = 1) : d142745 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142807 q = 1) : d146553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142807, d146553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12662 q selected
    | true =>
      simp only [d142807, d146553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12664 q selected
  have h2 (q : Pattern) (selected : d142809 q = 1) : d142809 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d142810 q = 1) : d146554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142810, d146554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142810, d146554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142811 q = 1) : d146555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142811, d146555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142811, d146555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142812 q = 1) : d146556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142812, d146556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142812, d146556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142816 q = 1) : d146560 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142816, d146560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142816, d146560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12665 q selected
  have h8 (q : Pattern) (selected : d142817 q = 1) : d146561 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142817, d146561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142817, d146561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d142818 q = 1) : d146562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142818, d146562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142818, d146562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d142819 q = 1) : d146563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142819, d146563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142819, d146563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d142820 q = 1) : d146564 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142820, d146564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142820, d146564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d142852 q = 1) : d146570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142852, d146570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142852, d146570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12669 q selected
  have h13 (q : Pattern) (selected : d142853 q = 1) : d146571 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142853, d146571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d142853, d146571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d142854 q = 1) : d146572 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142854, d146572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d142854, d146572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d142855 q = 1) : d146573 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142855, d146573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d142855, d146573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d142856 q = 1) : d146574 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142856, d146574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d142856, d146574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d142857 q = 1) : d146575 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d142857, d146575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142857, d146575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro12671 (p : Pattern) (selected : d142863 p = 1) : d146581 p = 1 := by
  have h0 (q : Pattern) (selected : d142730 q = 1) : d142730 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142858 q = 1) : d146576 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d142858, d146576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142858, d146576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12670 q selected
  have h3 (q : Pattern) (selected : d142859 q = 1) : d146577 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d142859, d146577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142859, d146577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142860 q = 1) : d146578 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d142860, d146578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142860, d146578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142861 q = 1) : d146579 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d142861, d146579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142861, d146579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142862 q = 1) : d146580 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d142862, d146580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142862, d146580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142863 q = 1) : d146581 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d142863, d146581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142863, d146581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro12672 (p : Pattern) (selected : d353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12673 (p : Pattern) (selected : d142909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142904 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12672 q selected
    | true =>
      simp only [d142904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12659 q selected
  have h2 (q : Pattern) (selected : d142905 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142906 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12659 q selected
    | true =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142907 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142909 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12674 (p : Pattern) (selected : d142915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12673 q selected
    | true =>
      simp only [d142910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12675 (p : Pattern) (selected : d142927 p = 1) : d146586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142884 q = 1) : d142884 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142890 q = 1) : d142890 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d142903 q = 1) : d142903 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d142916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12674 q selected
    | true =>
      simp only [d142916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
  have h5 (q : Pattern) (selected : d142917 q = 1) : d146582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142917, d146582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142917, d146582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142923 q = 1) : d142923 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d142924 q = 1) : d146583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142924, d146583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142924, d146583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142925 q = 1) : d146584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142925, d146584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142925, d146584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142926 q = 1) : d146585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142926, d146585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142926, d146585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142927 q = 1) : d146586 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142927, d146586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142927, d146586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro12676 (p : Pattern) (selected : d142939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12673 q selected
    | true =>
      simp only [d142910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12677 (p : Pattern) (selected : d142948 p = 1) : d146591 p = 1 := by
  have h0 (q : Pattern) (selected : d142884 q = 1) : d142884 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142890 q = 1) : d142890 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142903 q = 1) : d142903 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d142916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12674 q selected
    | true =>
      simp only [d142916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
  have h4 (q : Pattern) (selected : d142917 q = 1) : d146582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142917, d146582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142917, d146582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142923 q = 1) : d142923 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d142924 q = 1) : d146583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142924, d146583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142924, d146583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142925 q = 1) : d146584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142925, d146584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142925, d146584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142926 q = 1) : d146585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142926, d146585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142926, d146585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d142932 q = 1) : d142932 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d142936 q = 1) : d142936 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d142938 q = 1) : d142938 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d142940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12676 q selected
    | true =>
      simp only [d142940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
  have h13 (q : Pattern) (selected : d142941 q = 1) : d146587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142941, d146587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142941, d146587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d142944 q = 1) : d142944 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d142945 q = 1) : d146588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142945, d146588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d142945, d146588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142946 q = 1) : d146589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142946, d146589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142946, d146589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d142947 q = 1) : d146590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142947, d146590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142947, d146590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d142948 q = 1) : d146591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142948, d146591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d142948, d146591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro12678 (p : Pattern) (selected : d142957 p = 1) : d146598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142938 q = 1) : d142938 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12676 q selected
    | true =>
      simp only [d142940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
  have h3 (q : Pattern) (selected : d142941 q = 1) : d146587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142941, d146587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142941, d146587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142944 q = 1) : d142944 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142945 q = 1) : d146588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142945, d146588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142945, d146588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142955 q = 1) : d146596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142955, d146596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142955, d146596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142956 q = 1) : d146597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142956, d146597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142956, d146597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142957 q = 1) : d146598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d142957, d146598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142957, d146598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12679 (p : Pattern) (selected : d434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h2 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12680 (p : Pattern) (selected : d142983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142978 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12679 q selected
    | true =>
      simp only [d142978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12666 q selected
  have h2 (q : Pattern) (selected : d142979 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142980 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142834 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12666 q selected
    | true =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142835 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142836 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142981 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142837 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142982 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d142982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142983 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d142983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12681 (p : Pattern) (selected : d142989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142984 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12680 q selected
    | true =>
      simp only [d142984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142985 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142840 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12667 q selected
    | true =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142841 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142986 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d142986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142987 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d142987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d142987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142988 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d142988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d142989 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d142989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12682 (p : Pattern) (selected : d143001 p = 1) : d146608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142977 q = 1) : d142977 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12681 q selected
    | true =>
      simp only [d142990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12668 q selected
  have h3 (q : Pattern) (selected : d142991 q = 1) : d146604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142991, d146604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142991, d146604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142997 q = 1) : d142997 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142998 q = 1) : d146605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142998, d146605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142998, d146605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142999 q = 1) : d146606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142999, d146606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142999, d146606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143000 q = 1) : d146607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143000, d146607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143000, d146607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143001 q = 1) : d146608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143001, d146608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143001, d146608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12683 (p : Pattern) (selected : d143013 p = 1) : d146614 p = 1 := by
  have h0 (q : Pattern) (selected : d142878 q = 1) : d142878 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142949 q = 1) : d146592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142949, d146592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12675 q selected
    | true =>
      simp only [d142949, d146592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12677 q selected
  have h2 (q : Pattern) (selected : d142951 q = 1) : d142951 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d142952 q = 1) : d146593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142952, d146593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142952, d146593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d142953 q = 1) : d146594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142953, d146594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142953, d146594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142954 q = 1) : d146595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142954, d146595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142954, d146595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142958 q = 1) : d146599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142958, d146599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142958, d146599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12678 q selected
  have h8 (q : Pattern) (selected : d142960 q = 1) : d142960 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d142961 q = 1) : d146600 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142961, d146600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142961, d146600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142962 q = 1) : d146601 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142962, d146601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d142962, d146601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d142963 q = 1) : d146602 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d142963, d146602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d142963, d146602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d142964 q = 1) : d146603 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d142964, d146603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142964, d146603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143002 q = 1) : d146609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143002, d146609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143002, d146609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12682 q selected
  have h14 (q : Pattern) (selected : d143008 q = 1) : d143008 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143009 q = 1) : d146610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143009, d146610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143009, d146610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143010 q = 1) : d146611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143010, d146611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143010, d146611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d143011 q = 1) : d146612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143011, d146612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143011, d146612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d143012 q = 1) : d146613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143012, d146613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143012, d146613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d143013 q = 1) : d146614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143013, d146614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143013, d146614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro12684 (p : Pattern) (selected : d143019 p = 1) : d146620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143014 q = 1) : d146615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143014, d146615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143014, d146615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12683 q selected
  have h2 (q : Pattern) (selected : d143015 q = 1) : d146616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143015, d146616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143015, d146616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143016 q = 1) : d146617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143016, d146617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143016, d146617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143017 q = 1) : d146618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143017, d146618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143017, d146618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143018 q = 1) : d146619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143018, d146619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143018, d146619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143019 q = 1) : d146620 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143019, d146620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143019, d146620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12685 (p : Pattern) (selected : d577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d577 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12686 (p : Pattern) (selected : d877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d877 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12687 (p : Pattern) (selected : d143103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12685 q selected
    | true =>
      simp only [d143094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12686 q selected
  have h2 (q : Pattern) (selected : d143095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143097 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12686 q selected
    | true =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143098 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143101 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143102 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143103 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12688 (p : Pattern) (selected : d143107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143097 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12686 q selected
    | true =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143098 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143101 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143106 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143107 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12689 (p : Pattern) (selected : d143113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143104 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12687 q selected
    | true =>
      simp only [d143104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143105 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143110 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12690 (p : Pattern) (selected : d143117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12691 (p : Pattern) (selected : d143129 p = 1) : d146626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143071 q = 1) : d143071 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143080 q = 1) : d143080 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143093 q = 1) : d143093 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d143118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12689 q selected
    | true =>
      simp only [d143118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12690 q selected
  have h5 (q : Pattern) (selected : d143119 q = 1) : d146622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143119, d146622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143119, d146622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143125 q = 1) : d143125 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d143126 q = 1) : d146623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143126, d146623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143126, d146623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143127 q = 1) : d146624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143127, d146624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143127, d146624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143128 q = 1) : d146625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143128, d146625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143128, d146625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143129 q = 1) : d146626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143129, d146626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143129, d146626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro12692 (p : Pattern) (selected : d143143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143104 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12687 q selected
    | true =>
      simp only [d143104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143105 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143110 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12693 (p : Pattern) (selected : d143144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12694 (p : Pattern) (selected : d143153 p = 1) : d146631 p = 1 := by
  have h0 (q : Pattern) (selected : d143071 q = 1) : d143071 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143080 q = 1) : d143080 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143093 q = 1) : d143093 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12689 q selected
    | true =>
      simp only [d143118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12690 q selected
  have h4 (q : Pattern) (selected : d143119 q = 1) : d146622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143119, d146622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143119, d146622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143125 q = 1) : d143125 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d143126 q = 1) : d146623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143126, d146623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143126, d146623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143127 q = 1) : d146624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143127, d146624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143127, d146624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143128 q = 1) : d146625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143128, d146625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143128, d146625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143135 q = 1) : d143135 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d143140 q = 1) : d143140 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d143142 q = 1) : d143142 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d143145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12692 q selected
    | true =>
      simp only [d143145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12693 q selected
  have h13 (q : Pattern) (selected : d143146 q = 1) : d146627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143146, d146627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143146, d146627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143149 q = 1) : d143149 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143150 q = 1) : d146628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143150, d146628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143150, d146628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143151 q = 1) : d146629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143151, d146629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143151, d146629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143152 q = 1) : d146630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143152, d146630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143152, d146630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143153 q = 1) : d146631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143153, d146631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143153, d146631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro12695 (p : Pattern) (selected : d143173 p = 1) : d146638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143142 q = 1) : d143142 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12692 q selected
    | true =>
      simp only [d143145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12693 q selected
  have h3 (q : Pattern) (selected : d143146 q = 1) : d146627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143146, d146627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143146, d146627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143149 q = 1) : d143149 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143150 q = 1) : d146628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143150, d146628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143150, d146628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143171 q = 1) : d146636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143171, d146636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143171, d146636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143172 q = 1) : d146637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143172, d146637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143172, d146637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143173 q = 1) : d146638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143173, d146638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143173, d146638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12696 (p : Pattern) (selected : d694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12697 (p : Pattern) (selected : d1021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h2 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12698 (p : Pattern) (selected : d143223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143214 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12696 q selected
    | true =>
      simp only [d143214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12697 q selected
  have h2 (q : Pattern) (selected : d143215 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143216 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143217 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12697 q selected
    | true =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143218 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143220 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143221 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143222 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143223 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12699 (p : Pattern) (selected : d143227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143217 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12697 q selected
    | true =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143218 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143221 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143226 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143227 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12700 (p : Pattern) (selected : d143233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12698 q selected
    | true =>
      simp only [d143224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12699 q selected
    | true =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143231 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143232 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143233 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12701 (p : Pattern) (selected : d143237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12699 q selected
    | true =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143234 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143235 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143236 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143237 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12702 (p : Pattern) (selected : d143249 p = 1) : d146648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143213 q = 1) : d143213 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143238 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12700 q selected
    | true =>
      simp only [d143238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12701 q selected
  have h3 (q : Pattern) (selected : d143239 q = 1) : d146644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143239, d146644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143239, d146644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143245 q = 1) : d143245 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143246 q = 1) : d146645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143246, d146645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143246, d146645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143247 q = 1) : d146646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143247, d146646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143247, d146646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143248 q = 1) : d146647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143248, d146647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143248, d146647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143249 q = 1) : d146648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143249, d146648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143249, d146648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12703 (p : Pattern) (selected : d143266 p = 1) : d146654 p = 1 := by
  have h0 (q : Pattern) (selected : d143063 q = 1) : d143063 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143154 q = 1) : d146632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143154, d146632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12691 q selected
    | true =>
      simp only [d143154, d146632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12694 q selected
  have h2 (q : Pattern) (selected : d143167 q = 1) : d143167 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143168 q = 1) : d146633 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143168, d146633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143168, d146633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143169 q = 1) : d146634 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143169, d146634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143169, d146634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143170 q = 1) : d146635 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143170, d146635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143170, d146635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143174 q = 1) : d146639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143174, d146639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143174, d146639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12695 q selected
  have h8 (q : Pattern) (selected : d143176 q = 1) : d143176 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d143177 q = 1) : d146640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143177, d146640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143177, d146640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143178 q = 1) : d146641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143178, d146641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143178, d146641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d143179 q = 1) : d146642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143179, d146642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143179, d146642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d143180 q = 1) : d146643 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143180, d146643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143180, d146643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143250 q = 1) : d146649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143250, d146649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143250, d146649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12702 q selected
  have h14 (q : Pattern) (selected : d143261 q = 1) : d143261 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143262 q = 1) : d146650 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143262, d146650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143262, d146650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143263 q = 1) : d146651 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143263, d146651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143263, d146651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d143264 q = 1) : d146652 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143264, d146652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143264, d146652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d143265 q = 1) : d146653 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143265, d146653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143265, d146653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d143266 q = 1) : d146654 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143266, d146654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143266, d146654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro12704 (p : Pattern) (selected : d143272 p = 1) : d146660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143267 q = 1) : d146655 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143267, d146655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143267, d146655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12703 q selected
  have h2 (q : Pattern) (selected : d143268 q = 1) : d146656 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143268, d146656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143268, d146656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143269 q = 1) : d146657 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143269, d146657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143269, d146657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143270 q = 1) : d146658 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143270, d146658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143270, d146658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143271 q = 1) : d146659 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143271, d146659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143271, d146659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143272 q = 1) : d146660 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143272, d146660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143272, d146660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12705 (p : Pattern) (selected : d1268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1268 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12706 (p : Pattern) (selected : d1279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1279 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12707 (p : Pattern) (selected : d143360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12705 q selected
    | true =>
      simp only [d143351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12706 q selected
  have h2 (q : Pattern) (selected : d143352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143354 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12706 q selected
    | true =>
      simp only [d143354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143356 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143357 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143358 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143359 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143360 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12708 (p : Pattern) (selected : d143364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143354 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12706 q selected
    | true =>
      simp only [d143354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143356 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143358 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143363 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143364 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12709 (p : Pattern) (selected : d143370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12707 q selected
    | true =>
      simp only [d143361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12708 q selected
    | true =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12710 (p : Pattern) (selected : d143374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12708 q selected
    | true =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12711 (p : Pattern) (selected : d143386 p = 1) : d146667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143325 q = 1) : d143325 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143334 q = 1) : d143334 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143350 q = 1) : d143350 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d143375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12709 q selected
    | true =>
      simp only [d143375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12710 q selected
  have h5 (q : Pattern) (selected : d143376 q = 1) : d146663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143376, d146663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143376, d146663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143382 q = 1) : d143382 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d143383 q = 1) : d146664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143383, d146664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143383, d146664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143384 q = 1) : d146665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143384, d146665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143384, d146665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143385 q = 1) : d146666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143385, d146666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143385, d146666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143386 q = 1) : d146667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143386, d146667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143386, d146667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro12712 (p : Pattern) (selected : d143400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12707 q selected
    | true =>
      simp only [d143361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12708 q selected
    | true =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12713 (p : Pattern) (selected : d143401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12708 q selected
    | true =>
      simp only [d143365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12714 (p : Pattern) (selected : d143410 p = 1) : d146672 p = 1 := by
  have h0 (q : Pattern) (selected : d143325 q = 1) : d143325 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143334 q = 1) : d143334 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143350 q = 1) : d143350 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12709 q selected
    | true =>
      simp only [d143375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12710 q selected
  have h4 (q : Pattern) (selected : d143376 q = 1) : d146663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143376, d146663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143376, d146663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143382 q = 1) : d143382 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d143383 q = 1) : d146664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143383, d146664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143383, d146664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143384 q = 1) : d146665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143384, d146665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143384, d146665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143385 q = 1) : d146666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143385, d146666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143385, d146666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143392 q = 1) : d143392 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d143397 q = 1) : d143397 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d143399 q = 1) : d143399 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d143402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12712 q selected
    | true =>
      simp only [d143402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12713 q selected
  have h13 (q : Pattern) (selected : d143403 q = 1) : d146668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143403, d146668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143403, d146668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143406 q = 1) : d143406 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143407 q = 1) : d146669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143407, d146669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143407, d146669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143408 q = 1) : d146670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143408, d146670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143408, d146670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143409 q = 1) : d146671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143409, d146671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143409, d146671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143410 q = 1) : d146672 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143410, d146672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143410, d146672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro12715 (p : Pattern) (selected : d143430 p = 1) : d146679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143399 q = 1) : d143399 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12712 q selected
    | true =>
      simp only [d143402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12713 q selected
  have h3 (q : Pattern) (selected : d143403 q = 1) : d146668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143403, d146668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143403, d146668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143406 q = 1) : d143406 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143407 q = 1) : d146669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143407, d146669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143407, d146669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143428 q = 1) : d146677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143428, d146677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143428, d146677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143429 q = 1) : d146678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143429, d146678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143429, d146678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143430 q = 1) : d146679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143430, d146679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143430, d146679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12716 (p : Pattern) (selected : d1445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
  have h2 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12717 (p : Pattern) (selected : d1450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h2 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12718 (p : Pattern) (selected : d143483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12716 q selected
    | true =>
      simp only [d143474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12717 q selected
  have h2 (q : Pattern) (selected : d143475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12717 q selected
    | true =>
      simp only [d143477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143482 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143483 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12719 (p : Pattern) (selected : d143487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12717 q selected
    | true =>
      simp only [d143477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12720 (p : Pattern) (selected : d143493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12718 q selected
    | true =>
      simp only [d143484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12719 q selected
    | true =>
      simp only [d143488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143490 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143491 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143492 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143493 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12721 (p : Pattern) (selected : d143497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12719 q selected
    | true =>
      simp only [d143488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12722 (p : Pattern) (selected : d143509 p = 1) : d146689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143473 q = 1) : d143473 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12720 q selected
    | true =>
      simp only [d143498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12721 q selected
  have h3 (q : Pattern) (selected : d143499 q = 1) : d146685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143499, d146685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143499, d146685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143505 q = 1) : d143505 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143506 q = 1) : d146686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143506, d146686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143506, d146686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143507 q = 1) : d146687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143507, d146687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143507, d146687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143508 q = 1) : d146688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143508, d146688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143508, d146688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143509 q = 1) : d146689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143509, d146689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143509, d146689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12723 (p : Pattern) (selected : d143526 p = 1) : d146695 p = 1 := by
  have h0 (q : Pattern) (selected : d143317 q = 1) : d143317 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143411 q = 1) : d146673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143411, d146673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12711 q selected
    | true =>
      simp only [d143411, d146673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12714 q selected
  have h2 (q : Pattern) (selected : d143424 q = 1) : d143424 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143425 q = 1) : d146674 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143425, d146674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143425, d146674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143426 q = 1) : d146675 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143426, d146675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143426, d146675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143427 q = 1) : d146676 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143427, d146676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143427, d146676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143431 q = 1) : d146680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143431, d146680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143431, d146680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12715 q selected
  have h8 (q : Pattern) (selected : d143433 q = 1) : d143433 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d143434 q = 1) : d146681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143434, d146681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143434, d146681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143435 q = 1) : d146682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143435, d146682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143435, d146682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d143436 q = 1) : d146683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143436, d146683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143436, d146683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d143437 q = 1) : d146684 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143437, d146684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143437, d146684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143510 q = 1) : d146690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143510, d146690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143510, d146690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12722 q selected
  have h14 (q : Pattern) (selected : d143521 q = 1) : d143521 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143522 q = 1) : d146691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143522, d146691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143522, d146691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143523 q = 1) : d146692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143523, d146692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143523, d146692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d143524 q = 1) : d146693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143524, d146693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143524, d146693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d143525 q = 1) : d146694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143525, d146694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143525, d146694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d143526 q = 1) : d146695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143526, d146695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143526, d146695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro12724 (p : Pattern) (selected : d143532 p = 1) : d146701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143527 q = 1) : d146696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143527, d146696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143527, d146696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12723 q selected
  have h2 (q : Pattern) (selected : d143528 q = 1) : d146697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143528, d146697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143528, d146697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143529 q = 1) : d146698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143529, d146698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143529, d146698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143530 q = 1) : d146699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143530, d146699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143530, d146699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143531 q = 1) : d146700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143531, d146700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143531, d146700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143532 q = 1) : d146701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143532, d146701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143532, d146701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12725 (p : Pattern) (selected : d1744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1744 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12726 (p : Pattern) (selected : d1756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1756 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12727 (p : Pattern) (selected : d143621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143612 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12725 q selected
    | true =>
      simp only [d143612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12726 q selected
  have h2 (q : Pattern) (selected : d143613 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12726 q selected
    | true =>
      simp only [d143615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143619 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12728 (p : Pattern) (selected : d143625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12726 q selected
    | true =>
      simp only [d143615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143619 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143624 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143625 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12729 (p : Pattern) (selected : d143631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12727 q selected
    | true =>
      simp only [d143622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12728 q selected
    | true =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143628 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143629 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143631 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12730 (p : Pattern) (selected : d143635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12728 q selected
    | true =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12731 (p : Pattern) (selected : d143647 p = 1) : d146709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143586 q = 1) : d143586 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143595 q = 1) : d143595 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143611 q = 1) : d143611 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d143636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12729 q selected
    | true =>
      simp only [d143636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12730 q selected
  have h5 (q : Pattern) (selected : d143637 q = 1) : d146705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143637, d146705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143637, d146705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143643 q = 1) : d143643 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d143644 q = 1) : d146706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143644, d146706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143644, d146706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143645 q = 1) : d146707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143645, d146707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143645, d146707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143646 q = 1) : d146708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143646, d146708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143646, d146708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143647 q = 1) : d146709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143647, d146709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143647, d146709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro12732 (p : Pattern) (selected : d143661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12727 q selected
    | true =>
      simp only [d143622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12728 q selected
    | true =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143628 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143629 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12733 (p : Pattern) (selected : d143662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12728 q selected
    | true =>
      simp only [d143626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12734 (p : Pattern) (selected : d143671 p = 1) : d146714 p = 1 := by
  have h0 (q : Pattern) (selected : d143586 q = 1) : d143586 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143595 q = 1) : d143595 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143611 q = 1) : d143611 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12729 q selected
    | true =>
      simp only [d143636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12730 q selected
  have h4 (q : Pattern) (selected : d143637 q = 1) : d146705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143637, d146705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143637, d146705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143643 q = 1) : d143643 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d143644 q = 1) : d146706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143644, d146706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143644, d146706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143645 q = 1) : d146707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143645, d146707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143645, d146707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143646 q = 1) : d146708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143646, d146708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143646, d146708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d143653 q = 1) : d143653 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d143658 q = 1) : d143658 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d143660 q = 1) : d143660 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d143663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12732 q selected
    | true =>
      simp only [d143663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12733 q selected
  have h13 (q : Pattern) (selected : d143664 q = 1) : d146710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143664, d146710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d143664, d146710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d143667 q = 1) : d143667 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143668 q = 1) : d146711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143668, d146711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143668, d146711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143669 q = 1) : d146712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143669, d146712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143669, d146712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d143670 q = 1) : d146713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143670, d146713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143670, d146713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d143671 q = 1) : d146714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143671, d146714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d143671, d146714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro12735 (p : Pattern) (selected : d143691 p = 1) : d146721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143660 q = 1) : d143660 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12732 q selected
    | true =>
      simp only [d143663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12733 q selected
  have h3 (q : Pattern) (selected : d143664 q = 1) : d146710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143664, d146710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143664, d146710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143667 q = 1) : d143667 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143668 q = 1) : d146711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143668, d146711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143668, d146711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143689 q = 1) : d146719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143689, d146719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143689, d146719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143690 q = 1) : d146720 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143690, d146720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143690, d146720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143691 q = 1) : d146721 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143691, d146721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143691, d146721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12736 (p : Pattern) (selected : d1922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
  have h2 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12737 (p : Pattern) (selected : d1927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1924 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
  have h2 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12738 (p : Pattern) (selected : d143744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143735 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12736 q selected
    | true =>
      simp only [d143735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12737 q selected
  have h2 (q : Pattern) (selected : d143736 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143737 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12737 q selected
    | true =>
      simp only [d143738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143741 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12739 (p : Pattern) (selected : d143748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12737 q selected
    | true =>
      simp only [d143738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143747 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143748 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12740 (p : Pattern) (selected : d143754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12738 q selected
    | true =>
      simp only [d143745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12739 q selected
    | true =>
      simp only [d143749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro12741 (p : Pattern) (selected : d143758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12739 q selected
    | true =>
      simp only [d143749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12742 (p : Pattern) (selected : d143770 p = 1) : d146731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143734 q = 1) : d143734 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d143759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12740 q selected
    | true =>
      simp only [d143759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12741 q selected
  have h3 (q : Pattern) (selected : d143760 q = 1) : d146727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143760, d146727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143760, d146727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143766 q = 1) : d143766 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143767 q = 1) : d146728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143767, d146728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143767, d146728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143768 q = 1) : d146729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143768, d146729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143768, d146729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143769 q = 1) : d146730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143769, d146730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143769, d146730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143770 q = 1) : d146731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d143770, d146731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143770, d146731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro12743 (p : Pattern) (selected : d143787 p = 1) : d146737 p = 1 := by
  have h0 (q : Pattern) (selected : d143578 q = 1) : d143578 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143672 q = 1) : d146715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143672, d146715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12731 q selected
    | true =>
      simp only [d143672, d146715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12734 q selected
  have h2 (q : Pattern) (selected : d143685 q = 1) : d143685 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d143686 q = 1) : d146716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143686, d146716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d143686, d146716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d143687 q = 1) : d146717 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143687, d146717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143687, d146717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143688 q = 1) : d146718 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143688, d146718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143688, d146718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143692 q = 1) : d146722 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143692, d146722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143692, d146722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12735 q selected
  have h8 (q : Pattern) (selected : d143694 q = 1) : d143694 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d143695 q = 1) : d146723 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143695, d146723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143695, d146723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143696 q = 1) : d146724 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143696, d146724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143696, d146724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d143697 q = 1) : d146725 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143697, d146725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d143697, d146725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d143698 q = 1) : d146726 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143698, d146726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143698, d146726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d143771 q = 1) : d146732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143771, d146732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143771, d146732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12742 q selected
  have h14 (q : Pattern) (selected : d143782 q = 1) : d143782 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d143783 q = 1) : d146733 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d143783, d146733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d143783, d146733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d143784 q = 1) : d146734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d143784, d146734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d143784, d146734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d143785 q = 1) : d146735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d143785, d146735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d143785, d146735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d143786 q = 1) : d146736 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d143786, d146736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d143786, d146736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d143787 q = 1) : d146737 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d143787, d146737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d143787, d146737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro12744 (p : Pattern) (selected : d143793 p = 1) : d146743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143788 q = 1) : d146738 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d143788, d146738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143788, d146738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12743 q selected
  have h2 (q : Pattern) (selected : d143789 q = 1) : d146739 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d143789, d146739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143789, d146739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143790 q = 1) : d146740 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d143790, d146740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143790, d146740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143791 q = 1) : d146741 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d143791, d146741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143791, d146741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143792 q = 1) : d146742 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d143792, d146742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143792, d146742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143793 q = 1) : d146743 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d143793, d146743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143793, d146743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro12745 (p : Pattern) (selected : d2222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12746 (p : Pattern) (selected : d2234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2234 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro12747 (p : Pattern) (selected : d143883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143874 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12745 q selected
    | true =>
      simp only [d143874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12746 q selected
  have h2 (q : Pattern) (selected : d143875 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143876 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143877 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12746 q selected
    | true =>
      simp only [d143877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143878 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143879 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d143880 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143882 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143883 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d143883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro12748 (p : Pattern) (selected : d143887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143877 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12746 q selected
    | true =>
      simp only [d143877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143878 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143879 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d143881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143886 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d143886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d143886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d143887 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d143887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro12749 (p : Pattern) (selected : d143893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d143884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12747 q selected
    | true =>
      simp only [d143884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d143885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143888 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12748 q selected
    | true =>
      simp only [d143888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143889 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d143890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d143890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d143890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d143891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d143891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d143892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d143893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d143893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
