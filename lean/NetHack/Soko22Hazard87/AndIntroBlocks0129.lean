import NetHack.Soko22Hazard87.AndIntroBlocks0128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro32250 (p : Pattern) (ha : d112686 p = 1) (hb : d150457 p = 1) : d142573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150452 q = 1) : d142568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32249 q ha hb
    | true =>
      simp only [d150452, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31916 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150453 q = 1) : d142569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150454 q = 1) : d142570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150455 q = 1) : d142571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150456 q = 1) : d142572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150457 q = 1) : d142573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32251 (p : Pattern) (ha : d112686 p = 1) (hb : d150463 p = 1) : d142579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d112686 q = 1) : d142062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31906 q ha hb
    | true =>
      simp only [d13324, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31909 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d112686 q = 1) : d142063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150440 q = 1) : d142560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150441 q = 1) : d142561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150443 q = 1) : d142563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32248 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150444 q = 1) : d142564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150445 q = 1) : d142565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150446 q = 1) : d142566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150447 q = 1) : d142567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150458 q = 1) : d142574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32250 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150459 q = 1) : d142575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150460 q = 1) : d142576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150461 q = 1) : d142577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150462 q = 1) : d142578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150463 q = 1) : d142579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32252 (p : Pattern) (ha : d112686 p = 1) (hb : d150469 p = 1) : d142585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150464 q = 1) : d142580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32251 q ha hb
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150465 q = 1) : d142581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150466 q = 1) : d142582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150467 q = 1) : d142583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150468 q = 1) : d142584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150469 q = 1) : d142585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32253 (p : Pattern) (ha : d112686 p = 1) (hb : d150476 p = 1) : d142592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d112686 q = 1) : d142245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31949 q ha hb
    | true =>
      simp only [d13645, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31950 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d112686 q = 1) : d142246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d112686 q = 1) : d142247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d112686 q = 1) : d142248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d112686 q = 1) : d142249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150476 q = 1) : d142592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32254 (p : Pattern) (ha : d112686 p = 1) (hb : d150485 p = 1) : d142367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d112686 q = 1) : d142354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31981 q ha hb
    | true =>
      simp only [d13897, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d112686 q = 1) : d142355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d112686 q = 1) : d142362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31957 q ha hb
    | true =>
      simp only [d13850, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d112686 q = 1) : d142363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150482 q = 1) : d142364 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150483 q = 1) : d142365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150484 q = 1) : d142366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150485 q = 1) : d142367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32255 (p : Pattern) (ha : d112686 p = 1) (hb : d150491 p = 1) : d142603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150486 q = 1) : d142598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32254 q ha hb
    | true =>
      simp only [d150486, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31958 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150487 q = 1) : d142599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150488 q = 1) : d142600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150489 q = 1) : d142601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150490 q = 1) : d142602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150491 q = 1) : d142603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32256 (p : Pattern) (ha : d112686 p = 1) (hb : d150497 p = 1) : d142609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d112686 q = 1) : d142251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31948 q ha hb
    | true =>
      simp only [d13651, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31951 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d112686 q = 1) : d142252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150474 q = 1) : d142590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150475 q = 1) : d142591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150477 q = 1) : d142593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32253 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150478 q = 1) : d142594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150479 q = 1) : d142595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150480 q = 1) : d142596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150481 q = 1) : d142597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150492 q = 1) : d142604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32255 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150493 q = 1) : d142605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150494 q = 1) : d142606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150495 q = 1) : d142607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150496 q = 1) : d142608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150497 q = 1) : d142609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32257 (p : Pattern) (ha : d112686 p = 1) (hb : d150503 p = 1) : d142615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150498 q = 1) : d142610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32256 q ha hb
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150499 q = 1) : d142611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150500 q = 1) : d142612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150501 q = 1) : d142613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150502 q = 1) : d142614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150503 q = 1) : d142615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32258 (p : Pattern) (ha : d112686 p = 1) (hb : d150509 p = 1) : d142621 p = 1 := by
  have h0 (q : Pattern) (ha : d112686 q = 1) (hb : d150378 q = 1) : d142502 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32234 q ha hb
    | true =>
      simp only [d150378, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32238 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150405 q = 1) : d142529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32242 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150406 q = 1) : d142530 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150437 q = 1) : d142557 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32247 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150438 q = 1) : d142558 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150439 q = 1) : d142559 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150470 q = 1) : d142586 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32252 q ha hb
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150471 q = 1) : d142587 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150472 q = 1) : d142588 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150473 q = 1) : d142589 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150504 q = 1) : d142616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32257 q ha hb
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150505 q = 1) : d142617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150506 q = 1) : d142618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150507 q = 1) : d142619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150508 q = 1) : d142620 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112686 q = 1) (hb : d150509 q = 1) : d142621 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32259 (p : Pattern) (ha : d112686 p = 1) (hb : d150515 p = 1) : d142627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150510 q = 1) : d142622 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32258 q ha hb
    | true =>
      simp only [d150510, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150511 q = 1) : d142623 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150512 q = 1) : d142624 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150513 q = 1) : d142625 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150514 q = 1) : d142626 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150515 q = 1) : d142627 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32260 (p : Pattern) (ha : d112686 p = 1) (hb : d150521 p = 1) : d142633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150516 q = 1) : d142628 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32259 q ha hb
    | true =>
      simp only [d150516, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150517 q = 1) : d142629 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150518 q = 1) : d142630 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150519 q = 1) : d142631 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150520 q = 1) : d142632 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150521 q = 1) : d142633 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32261 (p : Pattern) (ha : d112686 p = 1) (hb : d150527 p = 1) : d142639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150522 q = 1) : d142634 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32260 q ha hb
    | true =>
      simp only [d150522, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150523 q = 1) : d142635 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150524 q = 1) : d142636 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150525 q = 1) : d142637 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150526 q = 1) : d142638 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150527 q = 1) : d142639 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32262 (p : Pattern) (ha : d112686 p = 1) (hb : d150533 p = 1) : d142645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150528 q = 1) : d142640 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32261 q ha hb
    | true =>
      simp only [d150528, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150529 q = 1) : d142641 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150530 q = 1) : d142642 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150531 q = 1) : d142643 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150532 q = 1) : d142644 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150533 q = 1) : d142645 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32263 (p : Pattern) (ha : d112686 p = 1) (hb : d150539 p = 1) : d142651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150534 q = 1) : d142646 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32262 q ha hb
    | true =>
      simp only [d150534, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150535 q = 1) : d142647 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150536 q = 1) : d142648 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150537 q = 1) : d142649 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150538 q = 1) : d142650 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150539 q = 1) : d142651 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32264 (p : Pattern) (ha : d112686 p = 1) (hb : d150545 p = 1) : d142657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150540 q = 1) : d142652 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32263 q ha hb
    | true =>
      simp only [d150540, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150541 q = 1) : d142653 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150542 q = 1) : d142654 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150543 q = 1) : d142655 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150544 q = 1) : d142656 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150545 q = 1) : d142657 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32265 (p : Pattern) (ha : d112686 p = 1) (hb : d150551 p = 1) : d142663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150546 q = 1) : d142658 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32264 q ha hb
    | true =>
      simp only [d150546, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150547 q = 1) : d142659 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150548 q = 1) : d142660 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150549 q = 1) : d142661 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150550 q = 1) : d142662 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150551 q = 1) : d142663 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32266 (p : Pattern) (ha : d107602 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107498 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
    | true =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d107592 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107592, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107599 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107599, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107600 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107600, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107601 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107601, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107602 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32267 (p : Pattern) (ha : d107621 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107498 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
    | true =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d107592 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107592, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107599 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107599, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107600 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107600, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107601 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107601, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107607 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107611 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107505 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31997 q ha hb
    | true =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d107614 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107614, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107618 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107618, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107619 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107619, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107620 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107620, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107621 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107621, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32268 (p : Pattern) (ha : d107630 p = 1) (hb : d142453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107505 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31997 q ha hb
    | true =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107614, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107618 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107628 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107629 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107630 q = 1) (hb : d142453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32269 (p : Pattern) (ha : d107659 p = 1) (hb : d142463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107535 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32001 q ha hb
    | true =>
      simp only [d107535, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d142459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107649, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107656 q = 1) (hb : d142460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107657 q = 1) (hb : d142461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107658 q = 1) (hb : d142462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107659 q = 1) (hb : d142463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32270 (p : Pattern) (ha : d107665 p = 1) (hb : d142469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107622 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32266 q ha hb
    | true =>
      simp only [d107622, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107625 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107625, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107626 q = 1) (hb : d142451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107626, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107627 q = 1) (hb : d142452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107627, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107631 q = 1) (hb : d142454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107631, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32268 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107632 q = 1) (hb : d142455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107632, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107633 q = 1) (hb : d142456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107633, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107634 q = 1) (hb : d142457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107634, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107635 q = 1) (hb : d142458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107635, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107660 q = 1) (hb : d142464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107660, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32269 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107661 q = 1) (hb : d142465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107661, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107662 q = 1) (hb : d142466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107662, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107663 q = 1) (hb : d142467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107663, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107664 q = 1) (hb : d142468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107664, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107665 q = 1) (hb : d142469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107665, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32271 (p : Pattern) (ha : d107671 p = 1) (hb : d142475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d107547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16176 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d107548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d107549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d107550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d107551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107666 q = 1) (hb : d142470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107666, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32270 q ha hb
  have h8 (q : Pattern) (ha : d107667 q = 1) (hb : d142471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107667, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107668 q = 1) (hb : d142472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107668, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107669 q = 1) (hb : d142473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107669, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107670 q = 1) (hb : d142474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107670, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107671 q = 1) (hb : d142475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107671, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro32272 (p : Pattern) (ha : d107748 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107689 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
    | true =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
  have h5 (q : Pattern) (ha : d107738 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107738, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107745 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107745, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107746 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107746, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107747 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107747, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107748 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32273 (p : Pattern) (ha : d107769 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107689 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
    | true =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
  have h4 (q : Pattern) (ha : d107738 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107738, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107745 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107745, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107746 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107746, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107747 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107747, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107759 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107699 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32030 q ha hb
    | true =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32031 q ha hb
  have h13 (q : Pattern) (ha : d107762 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107762, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107766 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107766, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107767 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107767, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107768 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107768, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107769 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107769, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32274 (p : Pattern) (ha : d107789 p = 1) (hb : d142478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107699 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32030 q ha hb
    | true =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32031 q ha hb
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107762, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107766 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107787 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107788 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107789 q = 1) (hb : d142478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32275 (p : Pattern) (ha : d107838 p = 1) (hb : d142489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107827 q = 1) (hb : d142484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107827, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32056 q ha hb
    | true =>
      simp only [d107827, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32059 q ha hb
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d142485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107828, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107835 q = 1) (hb : d142486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107836 q = 1) (hb : d142487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107837 q = 1) (hb : d142488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107838 q = 1) (hb : d142489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32276 (p : Pattern) (ha : d107851 p = 1) (hb : d142495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107707 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107770 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32272 q ha hb
    | true =>
      simp only [d107770, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107784 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107784, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107785 q = 1) (hb : d142476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107785, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107786 q = 1) (hb : d142477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107786, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107790 q = 1) (hb : d142479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107790, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32274 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107793 q = 1) (hb : d142480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107793, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107794 q = 1) (hb : d142481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107794, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107795 q = 1) (hb : d142482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107795, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107796 q = 1) (hb : d142483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107796, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107839 q = 1) (hb : d142490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107839, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32275 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107847 q = 1) (hb : d142491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107847, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107848 q = 1) (hb : d142492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107848, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107849 q = 1) (hb : d142493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107849, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107850 q = 1) (hb : d142494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107850, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107851 q = 1) (hb : d142495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107851, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32277 (p : Pattern) (ha : d107857 p = 1) (hb : d142501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d142496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32276 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d142497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d142498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d142499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d142500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d142501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32278 (p : Pattern) (ha : d107950 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107883 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
    | true =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
  have h5 (q : Pattern) (ha : d107932 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107932, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107947 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107947, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107948 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107948, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107949 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107949, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107950 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32279 (p : Pattern) (ha : d107971 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107883 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
    | true =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
  have h4 (q : Pattern) (ha : d107932 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107932, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107947 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107947, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107948 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107948, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107949 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107949, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107956 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107893 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32068 q ha hb
    | true =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32069 q ha hb
  have h13 (q : Pattern) (ha : d107964 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107964, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107968 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107968, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107969 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107969, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107970 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107970, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107971 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107971, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32280 (p : Pattern) (ha : d107991 p = 1) (hb : d142505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107893 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32068 q ha hb
    | true =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32069 q ha hb
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107964, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107968 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107989 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107990 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107991 q = 1) (hb : d142505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32281 (p : Pattern) (ha : d108055 p = 1) (hb : d142516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108036 q = 1) (hb : d142511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108036, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32095 q ha hb
    | true =>
      simp only [d108036, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32099 q ha hb
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d142512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108037, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108052 q = 1) (hb : d142513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108053 q = 1) (hb : d142514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108054 q = 1) (hb : d142515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108055 q = 1) (hb : d142516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32282 (p : Pattern) (ha : d108068 p = 1) (hb : d142522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107972 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32278 q ha hb
    | true =>
      simp only [d107972, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32279 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107986 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107986, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107987 q = 1) (hb : d142503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107987, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107988 q = 1) (hb : d142504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107988, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107992 q = 1) (hb : d142506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107992, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32280 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107994 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107995 q = 1) (hb : d142507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107995, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107996 q = 1) (hb : d142508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107996, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107997 q = 1) (hb : d142509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107997, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107998 q = 1) (hb : d142510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107998, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108056 q = 1) (hb : d142517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108056, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32281 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108064 q = 1) (hb : d142518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108064, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108065 q = 1) (hb : d142519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108065, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108066 q = 1) (hb : d142520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108066, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108067 q = 1) (hb : d142521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108067, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108068 q = 1) (hb : d142522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108068, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32283 (p : Pattern) (ha : d108074 p = 1) (hb : d142528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d142523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32282 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d142524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d142525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d142526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d142527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d142528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32284 (p : Pattern) (ha : d108168 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108101 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
    | true =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
  have h5 (q : Pattern) (ha : d108150 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108150, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108165 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108165, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108166 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108166, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108167 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108167, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108168 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32285 (p : Pattern) (ha : d108189 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108101 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
    | true =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
  have h4 (q : Pattern) (ha : d108150 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108150, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108165 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108165, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108166 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108166, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108167 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108167, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108174 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108179 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108111 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32108 q ha hb
    | true =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32109 q ha hb
  have h13 (q : Pattern) (ha : d108182 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108182, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108186 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108186, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108187 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108187, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108188 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108188, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108189 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108189, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32286 (p : Pattern) (ha : d108209 p = 1) (hb : d142533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108111 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32108 q ha hb
    | true =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32109 q ha hb
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108182, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108186 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108207 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108208 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108209 q = 1) (hb : d142533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32287 (p : Pattern) (ha : d108273 p = 1) (hb : d142544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108254 q = 1) (hb : d142539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108254, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32135 q ha hb
    | true =>
      simp only [d108254, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32139 q ha hb
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d142540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108255, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108270 q = 1) (hb : d142541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108271 q = 1) (hb : d142542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108272 q = 1) (hb : d142543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108273 q = 1) (hb : d142544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32288 (p : Pattern) (ha : d108286 p = 1) (hb : d142550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108190 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32284 q ha hb
    | true =>
      simp only [d108190, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32285 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108204 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108204, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108205 q = 1) (hb : d142531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108205, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108206 q = 1) (hb : d142532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108206, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108210 q = 1) (hb : d142534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108210, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32286 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108212 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108213 q = 1) (hb : d142535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108213, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108214 q = 1) (hb : d142536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108214, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108215 q = 1) (hb : d142537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108215, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108216 q = 1) (hb : d142538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108216, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108274 q = 1) (hb : d142545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108274, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32287 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108281 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108282 q = 1) (hb : d142546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108282, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108283 q = 1) (hb : d142547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108283, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108284 q = 1) (hb : d142548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108284, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108285 q = 1) (hb : d142549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108285, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108286 q = 1) (hb : d142550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108286, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32289 (p : Pattern) (ha : d108292 p = 1) (hb : d142556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d142551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32288 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d142552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d142553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d142554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d142555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d142556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32290 (p : Pattern) (ha : d108387 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108320 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
    | true =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
  have h5 (q : Pattern) (ha : d108369 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108369, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108384 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108384, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108385 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108385, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108386 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108386, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108387 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32291 (p : Pattern) (ha : d108408 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108320 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
    | true =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
  have h4 (q : Pattern) (ha : d108369 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108369, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108384 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108384, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108385 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108385, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108386 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108386, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108398 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108330 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32148 q ha hb
    | true =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32149 q ha hb
  have h13 (q : Pattern) (ha : d108401 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108401, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108405 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108405, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108406 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108406, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108407 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108407, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108408 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108408, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32292 (p : Pattern) (ha : d108428 p = 1) (hb : d142562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108330 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32148 q ha hb
    | true =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32149 q ha hb
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108401, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108405 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108426 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108427 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108428 q = 1) (hb : d142562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32293 (p : Pattern) (ha : d108492 p = 1) (hb : d142573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108473 q = 1) (hb : d142568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108473, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32175 q ha hb
    | true =>
      simp only [d108473, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32179 q ha hb
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d142569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108474, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108489 q = 1) (hb : d142570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108490 q = 1) (hb : d142571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108491 q = 1) (hb : d142572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108492 q = 1) (hb : d142573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32294 (p : Pattern) (ha : d108505 p = 1) (hb : d142579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108409 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32290 q ha hb
    | true =>
      simp only [d108409, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32291 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108423 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108423, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108424 q = 1) (hb : d142560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108424, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108425 q = 1) (hb : d142561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108425, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108429 q = 1) (hb : d142563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108429, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32292 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108431 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108432 q = 1) (hb : d142564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108432, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108433 q = 1) (hb : d142565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108433, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108434 q = 1) (hb : d142566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108434, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108435 q = 1) (hb : d142567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108435, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108493 q = 1) (hb : d142574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108493, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32293 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108500 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108501 q = 1) (hb : d142575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108501, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108502 q = 1) (hb : d142576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108502, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108503 q = 1) (hb : d142577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108503, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108504 q = 1) (hb : d142578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108504, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108505 q = 1) (hb : d142579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108505, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32295 (p : Pattern) (ha : d108511 p = 1) (hb : d142585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d142580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32294 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d142581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d142582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d142583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d142584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d142585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32296 (p : Pattern) (ha : d108607 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108540 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
    | true =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
  have h5 (q : Pattern) (ha : d108589 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108589, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108604 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108604, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108605 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108605, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108606 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108606, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108607 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32297 (p : Pattern) (ha : d108628 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108540 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
    | true =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
  have h4 (q : Pattern) (ha : d108589 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108589, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108604 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108604, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108605 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108605, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108606 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108606, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108550 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32188 q ha hb
    | true =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32189 q ha hb
  have h13 (q : Pattern) (ha : d108621 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108621, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108625 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108625, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108626 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108626, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108627 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108627, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108628 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108628, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32298 (p : Pattern) (ha : d108648 p = 1) (hb : d142592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108550 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32188 q ha hb
    | true =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32189 q ha hb
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108621, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108625 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108646 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108647 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108648 q = 1) (hb : d142592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32299 (p : Pattern) (ha : d108712 p = 1) (hb : d142603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108693 q = 1) (hb : d142598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108693, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32215 q ha hb
    | true =>
      simp only [d108693, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32219 q ha hb
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d142599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108694, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108709 q = 1) (hb : d142600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108710 q = 1) (hb : d142601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108711 q = 1) (hb : d142602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108712 q = 1) (hb : d142603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32300 (p : Pattern) (ha : d108725 p = 1) (hb : d142609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108629 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32296 q ha hb
    | true =>
      simp only [d108629, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32297 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108643 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108643, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108644 q = 1) (hb : d142590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108644, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108645 q = 1) (hb : d142591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108645, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108649 q = 1) (hb : d142593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108649, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32298 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108652 q = 1) (hb : d142594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108652, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108653 q = 1) (hb : d142595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108653, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108654 q = 1) (hb : d142596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108654, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108655 q = 1) (hb : d142597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108655, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108713 q = 1) (hb : d142604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108713, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32299 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108720 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108721 q = 1) (hb : d142605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108721, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108722 q = 1) (hb : d142606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108722, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108723 q = 1) (hb : d142607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108723, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108724 q = 1) (hb : d142608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108724, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108725 q = 1) (hb : d142609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108725, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32301 (p : Pattern) (ha : d108731 p = 1) (hb : d142615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d142610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32300 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d142611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d142612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d142613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d142614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d142615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32302 (p : Pattern) (ha : d108737 p = 1) (hb : d142621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d142502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32271 q ha hb
    | true =>
      simp only [d107858, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32277 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d142529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32283 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d142530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d142557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32289 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d142558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d142559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d142586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32295 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d142587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d142588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d142589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d142616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32301 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d142617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d142618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d142619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d142620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d142621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32303 (p : Pattern) (ha : d108743 p = 1) (hb : d142627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d142622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32302 q ha hb
    | true =>
      simp only [d108738, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d142623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d142624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d142625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d142626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d142627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32304 (p : Pattern) (ha : d108749 p = 1) (hb : d142633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d142628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32303 q ha hb
    | true =>
      simp only [d108744, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d142629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d142630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d142631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d142632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d142633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32305 (p : Pattern) (ha : d108755 p = 1) (hb : d142639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d142634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32304 q ha hb
    | true =>
      simp only [d108750, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d142635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d142636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d142637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d142638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d142639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32306 (p : Pattern) (ha : d108761 p = 1) (hb : d142645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d142640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32305 q ha hb
    | true =>
      simp only [d108756, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d142641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d142642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d142643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d142644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d142645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32307 (p : Pattern) (ha : d108767 p = 1) (hb : d142651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d142646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32306 q ha hb
    | true =>
      simp only [d108762, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d142647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d142648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d142649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d142650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d142651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32308 (p : Pattern) (ha : d108773 p = 1) (hb : d142657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d142652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32307 q ha hb
    | true =>
      simp only [d108768, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d142653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d142654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d142655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d142656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d142657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32309 (p : Pattern) (ha : d108779 p = 1) (hb : d142663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d142658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32308 q ha hb
    | true =>
      simp only [d108774, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d142659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d142660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d142661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d142662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d142663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32310 (p : Pattern) (ha : d108822 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108818 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108818, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108819 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108819, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108820 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108820, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108821 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108821, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108822 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32311 (p : Pattern) (ha : d108827 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108818 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108818, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108819 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108819, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108820 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108820, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108821 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108821, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10783 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10787 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108823 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108823, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108824 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108824, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108825 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108825, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108826 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108826, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108827 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108827, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32312 (p : Pattern) (ha : d108834 p = 1) (hb : d142453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108823 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108824, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d142453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32313 (p : Pattern) (ha : d108844 p = 1) (hb : d142463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108840 q = 1) (hb : d142459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10846 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d142460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108841, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d142461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d142462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d142463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32314 (p : Pattern) (ha : d108850 p = 1) (hb : d142469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10729 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108828 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32310 q ha hb
    | true =>
      simp only [d108828, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32311 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108829 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108829, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108830 q = 1) (hb : d142451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108830, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108831 q = 1) (hb : d142452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108831, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108835 q = 1) (hb : d142454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108835, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32312 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108836 q = 1) (hb : d142455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108836, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108837 q = 1) (hb : d142456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108837, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108838 q = 1) (hb : d142457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108838, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108839 q = 1) (hb : d142458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108839, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108845 q = 1) (hb : d142464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108845, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32313 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108846 q = 1) (hb : d142465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108846, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108847 q = 1) (hb : d142466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108847, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108848 q = 1) (hb : d142467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108848, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108849 q = 1) (hb : d142468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108849, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108850 q = 1) (hb : d142469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108850, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32315 (p : Pattern) (ha : d108856 p = 1) (hb : d142475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16225 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d142470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32314 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d142471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d142472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d142473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d142474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d142475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d108856, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro32316 (p : Pattern) (ha : d108861 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108857 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108857, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108858 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108858, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108859 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108859, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108860 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108860, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108861 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32317 (p : Pattern) (ha : d108866 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108857 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108857, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108858 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108858, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108859 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108859, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108860 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108860, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108862 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108862, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108863 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108863, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108864 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108864, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108865 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108865, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108866 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108866, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32318 (p : Pattern) (ha : d108873 p = 1) (hb : d142478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108862 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108863, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d142478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32319 (p : Pattern) (ha : d108883 p = 1) (hb : d142489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108879 q = 1) (hb : d142485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11067 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d142486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108880, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d142487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d142488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d142489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32320 (p : Pattern) (ha : d108889 p = 1) (hb : d142495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10898 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108867 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32316 q ha hb
    | true =>
      simp only [d108867, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32317 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108868 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108868, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108869 q = 1) (hb : d142476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108869, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108870 q = 1) (hb : d142477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108870, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108874 q = 1) (hb : d142479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108874, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32318 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11008 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108875 q = 1) (hb : d142480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108875, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108876 q = 1) (hb : d142481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108876, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108877 q = 1) (hb : d142482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108877, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108878 q = 1) (hb : d142483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108878, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108884 q = 1) (hb : d142490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108884, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32319 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108885 q = 1) (hb : d142491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108885, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108886 q = 1) (hb : d142492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108886, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108887 q = 1) (hb : d142493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108887, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108888 q = 1) (hb : d142494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108888, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108889 q = 1) (hb : d142495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108889, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32321 (p : Pattern) (ha : d108895 p = 1) (hb : d142501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d142496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32320 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d142497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d142498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d142499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d142500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d142501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32322 (p : Pattern) (ha : d108901 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108897 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108897, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108898 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108898, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108899 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108899, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108900 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108900, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108901 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32323 (p : Pattern) (ha : d108906 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108897 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108897, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108898 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108898, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108899 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108899, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108900 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108900, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11223 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108902 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108902, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108903 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108903, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108904 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108904, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108905 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108905, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108906 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108906, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32324 (p : Pattern) (ha : d108913 p = 1) (hb : d142505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108902 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108903, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d142505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32325 (p : Pattern) (ha : d108923 p = 1) (hb : d142516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11296 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108919 q = 1) (hb : d142512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d142513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108920, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d142514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d142515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d142516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32326 (p : Pattern) (ha : d108929 p = 1) (hb : d142522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108907 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32322 q ha hb
    | true =>
      simp only [d108907, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32323 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108908 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108908, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108909 q = 1) (hb : d142503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108909, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108910 q = 1) (hb : d142504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108910, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108914 q = 1) (hb : d142506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108914, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32324 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108915 q = 1) (hb : d142507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108915, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108916 q = 1) (hb : d142508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108916, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108917 q = 1) (hb : d142509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108917, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108918 q = 1) (hb : d142510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108918, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108924 q = 1) (hb : d142517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108924, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32325 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108925 q = 1) (hb : d142518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108925, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108926 q = 1) (hb : d142519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108926, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108927 q = 1) (hb : d142520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108927, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108928 q = 1) (hb : d142521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108928, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108929 q = 1) (hb : d142522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108929, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32327 (p : Pattern) (ha : d108935 p = 1) (hb : d142528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d142523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32326 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d142524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d142525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d142526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d142527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d142528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32328 (p : Pattern) (ha : d108942 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108938 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108938, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108939 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108939, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108940 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108940, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108941 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108941, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108942 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32329 (p : Pattern) (ha : d108947 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108938 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108938, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108939 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108939, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108940 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108940, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108941 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108941, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108943 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108943, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108944 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108944, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108945 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108945, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108946 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108946, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108947 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108947, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32330 (p : Pattern) (ha : d108954 p = 1) (hb : d142533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108943 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108944, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d142533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32331 (p : Pattern) (ha : d108964 p = 1) (hb : d142544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108960 q = 1) (hb : d142540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11606 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d142541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108961, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d142542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d142543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d142544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32332 (p : Pattern) (ha : d108970 p = 1) (hb : d142550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11408 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108948 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32328 q ha hb
    | true =>
      simp only [d108948, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32329 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108949 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108949, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108950 q = 1) (hb : d142531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108950, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108951 q = 1) (hb : d142532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108951, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108955 q = 1) (hb : d142534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108955, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32330 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108956 q = 1) (hb : d142535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108956, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108957 q = 1) (hb : d142536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108957, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108958 q = 1) (hb : d142537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108958, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108959 q = 1) (hb : d142538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108959, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108965 q = 1) (hb : d142545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108965, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32331 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11622 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108966 q = 1) (hb : d142546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108966, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108967 q = 1) (hb : d142547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108967, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108968 q = 1) (hb : d142548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108968, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108969 q = 1) (hb : d142549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108969, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108970 q = 1) (hb : d142550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108970, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32333 (p : Pattern) (ha : d108976 p = 1) (hb : d142556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d142551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32332 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d142552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d142553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d142554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d142555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d142556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32334 (p : Pattern) (ha : d108984 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108980 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108980, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108981 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108981, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108982 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108982, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108983 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108983, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108984 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32335 (p : Pattern) (ha : d108989 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108980 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108980, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108981 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108981, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108982 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108982, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108983 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108983, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108985 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108985, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108986 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108986, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108987 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108987, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108988 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108988, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108989 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108989, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32336 (p : Pattern) (ha : d108996 p = 1) (hb : d142562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108985 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108986, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d142562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32337 (p : Pattern) (ha : d109006 p = 1) (hb : d142573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109002 q = 1) (hb : d142569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d142570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109003, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d142571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d142572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d142573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32338 (p : Pattern) (ha : d109012 p = 1) (hb : d142579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108990 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32334 q ha hb
    | true =>
      simp only [d108990, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108991 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108991, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108992 q = 1) (hb : d142560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108992, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108993 q = 1) (hb : d142561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108993, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108997 q = 1) (hb : d142563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108997, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32336 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108998 q = 1) (hb : d142564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108998, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108999 q = 1) (hb : d142565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108999, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109000 q = 1) (hb : d142566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109000, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109001 q = 1) (hb : d142567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109001, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109007 q = 1) (hb : d142574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109007, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32337 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109008 q = 1) (hb : d142575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109008, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109009 q = 1) (hb : d142576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109009, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109010 q = 1) (hb : d142577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109010, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109011 q = 1) (hb : d142578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109011, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109012 q = 1) (hb : d142579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109012, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32339 (p : Pattern) (ha : d109018 p = 1) (hb : d142585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d142580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32338 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d142581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d142582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d142583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d142584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d142585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32340 (p : Pattern) (ha : d109027 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109023 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d109023, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d109024 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109024, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d109025 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109025, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109026 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109026, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109027 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro32341 (p : Pattern) (ha : d109032 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109023 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109023, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109024 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109024, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d109025 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109025, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109026 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109026, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12031 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d109028 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d109028, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109029 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109029, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109030 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109030, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109031 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109031, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109032 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109032, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro32342 (p : Pattern) (ha : d109039 p = 1) (hb : d142592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109028 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109029, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d142592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32343 (p : Pattern) (ha : d109049 p = 1) (hb : d142603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109045 q = 1) (hb : d142599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d142600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109046, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d142601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d142602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d142603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32344 (p : Pattern) (ha : d109055 p = 1) (hb : d142609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109033 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32340 q ha hb
    | true =>
      simp only [d109033, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109034 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109034, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109035 q = 1) (hb : d142590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109035, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109036 q = 1) (hb : d142591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109036, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109040 q = 1) (hb : d142593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109040, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32342 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d109041 q = 1) (hb : d142594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109041, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d109042 q = 1) (hb : d142595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109042, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109043 q = 1) (hb : d142596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109043, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109044 q = 1) (hb : d142597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109044, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109050 q = 1) (hb : d142604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109050, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32343 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109051 q = 1) (hb : d142605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109051, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109052 q = 1) (hb : d142606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109052, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109053 q = 1) (hb : d142607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109053, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109054 q = 1) (hb : d142608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109054, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109055 q = 1) (hb : d142609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109055, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro32345 (p : Pattern) (ha : d109061 p = 1) (hb : d142615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d142610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32344 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d142611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d142612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d142613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d142614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d142615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32346 (p : Pattern) (ha : d109067 p = 1) (hb : d142621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d142502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32315 q ha hb
    | true =>
      simp only [d108896, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32321 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d142529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32327 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d142530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d142557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32333 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d142558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d142559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d142586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32339 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d142587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d142588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d142589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d142616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32345 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d142617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d142618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d142619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d142620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d142621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro32347 (p : Pattern) (ha : d109073 p = 1) (hb : d142627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d142622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32346 q ha hb
    | true =>
      simp only [d109068, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d142623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d142624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d142625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d142626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d142627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32348 (p : Pattern) (ha : d109079 p = 1) (hb : d142633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d142628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32347 q ha hb
    | true =>
      simp only [d109074, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d142629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d142630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d142631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d142632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d142633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32349 (p : Pattern) (ha : d109085 p = 1) (hb : d142639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d142634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32348 q ha hb
    | true =>
      simp only [d109080, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d142635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d142636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d142637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d142638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d142639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32350 (p : Pattern) (ha : d109091 p = 1) (hb : d142645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d142640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32349 q ha hb
    | true =>
      simp only [d109086, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d142641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d142642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d142643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d142644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d142645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32351 (p : Pattern) (ha : d109097 p = 1) (hb : d142651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d142646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32350 q ha hb
    | true =>
      simp only [d109092, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d142647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d142648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d142649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d142650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d142651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32352 (p : Pattern) (ha : d109103 p = 1) (hb : d142657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d142652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32351 q ha hb
    | true =>
      simp only [d109098, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d142653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d142654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d142655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d142656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d142657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32353 (p : Pattern) (ha : d109109 p = 1) (hb : d142663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d142658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32352 q ha hb
    | true =>
      simp only [d109104, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d142659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d142660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d142661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d142662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d142663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32354 (p : Pattern) (ha : d12227 p = 1) (hb : d135431 p = 1) : d138044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4819 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4820 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4821 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12225 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12225, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12226 q = 1) (hb : d135431 q = 1) : d138043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12226, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12227 q = 1) (hb : d135431 q = 1) : d138044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12227, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32355 (p : Pattern) (ha : d12233 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12233 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32356 (p : Pattern) (ha : d115242 p = 1) (hb : d135431 p = 1) : d138056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
    | true =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d135431 q = 1) : d138053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d135431 q = 1) : d138054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d135431 q = 1) : d138055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115242 q = 1) (hb : d135431 q = 1) : d138056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32357 (p : Pattern) (ha : d12240 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12240 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12240, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32358 (p : Pattern) (ha : d115247 p = 1) (hb : d135431 p = 1) : d138063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
    | true =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d135431 q = 1) : d138053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d135431 q = 1) : d138054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d135431 q = 1) : d138055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24121 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24122 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12241 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
    | true =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h23 (q : Pattern) (ha : d115243 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115243, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115244 q = 1) (hb : d135431 q = 1) : d138060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115244, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115245 q = 1) (hb : d135431 q = 1) : d138061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115245, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115246 q = 1) (hb : d135431 q = 1) : d138062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115246, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115247 q = 1) (hb : d135431 q = 1) : d138063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115247, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32359 (p : Pattern) (ha : d115254 p = 1) (hb : d135431 p = 1) : d138068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
    | true =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h2 (q : Pattern) (ha : d115243 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115243, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d135431 q = 1) : d138060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115244, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d135431 q = 1) : d138061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d135431 q = 1) : d138062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d135431 q = 1) : d138068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32360 (p : Pattern) (ha : d12261 p = 1) (hb : d135431 p = 1) : d138079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6079 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6080 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6081 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12259 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12259, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12260 q = 1) (hb : d135431 q = 1) : d138078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12260, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12261 q = 1) (hb : d135431 q = 1) : d138079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12261, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32361 (p : Pattern) (ha : d12267 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32360 q ha hb
    | true =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24104 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12264 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12265 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12265, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12266 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12266, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12267 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12267, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32362 (p : Pattern) (ha : d115264 p = 1) (hb : d135431 p = 1) : d138091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32361 q ha hb
    | true =>
      simp only [d12268, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
  have h2 (q : Pattern) (ha : d115260 q = 1) (hb : d135431 q = 1) : d138087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115260, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d135431 q = 1) : d138088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115261, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d135431 q = 1) : d138089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d135431 q = 1) : d138090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d135431 q = 1) : d138091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32363 (p : Pattern) (ha : d115270 p = 1) (hb : d135431 p = 1) : d138097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24108 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24108 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24109 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115248 q = 1) (hb : d135431 q = 1) : d138064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32356 q ha hb
    | true =>
      simp only [d115248, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32358 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24110 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d115249 q = 1) (hb : d135431 q = 1) : d138065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115249, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115250 q = 1) (hb : d135431 q = 1) : d138066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115250, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115251 q = 1) (hb : d135431 q = 1) : d138067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115251, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115255 q = 1) (hb : d135431 q = 1) : d138069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115255, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32359 q ha hb
  have h12 (q : Pattern) (ha : d115256 q = 1) (hb : d135431 q = 1) : d138070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115256, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d115257 q = 1) (hb : d135431 q = 1) : d138071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115257, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115258 q = 1) (hb : d135431 q = 1) : d138072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115258, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115259 q = 1) (hb : d135431 q = 1) : d138073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115259, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115265 q = 1) (hb : d135431 q = 1) : d138092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115265, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32362 q ha hb
  have h17 (q : Pattern) (ha : d115266 q = 1) (hb : d135431 q = 1) : d138093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115266, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d115267 q = 1) (hb : d135431 q = 1) : d138094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115267, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d115268 q = 1) (hb : d135431 q = 1) : d138095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115268, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d115269 q = 1) (hb : d135431 q = 1) : d138096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115269, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115270 q = 1) (hb : d135431 q = 1) : d138097 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115270, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro32364 (p : Pattern) (ha : d12289 p = 1) (hb : d135431 p = 1) : d138107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
    | true =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12289 q = 1) (hb : d135431 q = 1) : d138107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32365 (p : Pattern) (ha : d12296 p = 1) (hb : d135431 p = 1) : d138114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
    | true =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12241 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
    | true =>
      simp only [d12241, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h7 (q : Pattern) (ha : d12292 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12293 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12293, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12294 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12295 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12296 q = 1) (hb : d135431 q = 1) : d138114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12296, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32366 (p : Pattern) (ha : d12373 p = 1) (hb : d135431 p = 1) : d138165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
    | true =>
      simp only [d12234, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12373 q = 1) (hb : d135431 q = 1) : d138165 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12373, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32367 (p : Pattern) (ha : d12301 p = 1) (hb : d135431 p = 1) : d138119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12301 q = 1) (hb : d135431 q = 1) : d138119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32368 (p : Pattern) (ha : d12308 p = 1) (hb : d135431 p = 1) : d138126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12308 q = 1) (hb : d135431 q = 1) : d138126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32369 (p : Pattern) (ha : d12318 p = 1) (hb : d135431 p = 1) : d138135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12313 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12314 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12315 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4818 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4819 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4820 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4821 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12316 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d31 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12225 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12225, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12317 q = 1) (hb : d135431 q = 1) : d138134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12317, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12318 q = 1) (hb : d135431 q = 1) : d138135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12318, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro32370 (p : Pattern) (ha : d12324 p = 1) (hb : d135431 p = 1) : d138141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32369 q ha hb
    | true =>
      simp only [d12319, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d135431 q = 1) : d138141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32371 (p : Pattern) (ha : d12344 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32372 (p : Pattern) (ha : d115280 p = 1) (hb : d135431 p = 1) : d138147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d135431 q = 1) : d138120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32367 q ha hb
    | true =>
      simp only [d12302, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d135431 q = 1) : d138121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d135431 q = 1) : d138122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d135431 q = 1) : d138123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d135431 q = 1) : d138127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32368 q ha hb
    | true =>
      simp only [d12309, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d135431 q = 1) : d138128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d135431 q = 1) : d138129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32370 q ha hb
    | true =>
      simp only [d12325, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d135431 q = 1) : d138143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32371 q ha hb
    | true =>
      simp only [d12345, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d135431 q = 1) : d138144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d135431 q = 1) : d138145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d135431 q = 1) : d138146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115280 q = 1) (hb : d135431 q = 1) : d138147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32373 (p : Pattern) (ha : d12351 p = 1) (hb : d135431 p = 1) : d138148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12351 q = 1) (hb : d135431 q = 1) : d138148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12351, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32374 (p : Pattern) (ha : d12356 p = 1) (hb : d135431 p = 1) : d138153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12356 q = 1) (hb : d135431 q = 1) : d138153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12356, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32375 (p : Pattern) (ha : d12360 p = 1) (hb : d135431 p = 1) : d138157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32369 q ha hb
    | true =>
      simp only [d12319, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d135431 q = 1) : d138157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32376 (p : Pattern) (ha : d12365 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32354 q ha hb
    | true =>
      simp only [d12228, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32377 (p : Pattern) (ha : d115285 p = 1) (hb : d135431 p = 1) : d138163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d135431 q = 1) : d138120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32367 q ha hb
    | true =>
      simp only [d12302, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d135431 q = 1) : d138121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d135431 q = 1) : d138122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d135431 q = 1) : d138123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d135431 q = 1) : d138127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32368 q ha hb
    | true =>
      simp only [d12309, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d135431 q = 1) : d138128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d135431 q = 1) : d138129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32370 q ha hb
    | true =>
      simp only [d12325, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32355 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d135431 q = 1) : d138143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32371 q ha hb
    | true =>
      simp only [d12345, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d135431 q = 1) : d138144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d135431 q = 1) : d138145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d135431 q = 1) : d138146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12352 q = 1) (hb : d135431 q = 1) : d138149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32373 q ha hb
    | true =>
      simp only [d12352, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24121 q ha hb
  have h16 (q : Pattern) (ha : d12353 q = 1) (hb : d135431 q = 1) : d138150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12354 q = 1) (hb : d135431 q = 1) : d138151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12354, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12355 q = 1) (hb : d135431 q = 1) : d138152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12357 q = 1) (hb : d135431 q = 1) : d138154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32374 q ha hb
    | true =>
      simp only [d12357, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24122 q ha hb
  have h20 (q : Pattern) (ha : d12358 q = 1) (hb : d135431 q = 1) : d138155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12359 q = 1) (hb : d135431 q = 1) : d138156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12359, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12361 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32375 q ha hb
    | true =>
      simp only [d12361, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
  have h23 (q : Pattern) (ha : d115281 q = 1) (hb : d135431 q = 1) : d138159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115281, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12366 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32376 q ha hb
    | true =>
      simp only [d12366, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12367 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12367, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115282 q = 1) (hb : d135431 q = 1) : d138160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115282, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115283 q = 1) (hb : d135431 q = 1) : d138161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115283, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115284 q = 1) (hb : d135431 q = 1) : d138162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115284, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115285 q = 1) (hb : d135431 q = 1) : d138163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115285, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32378 (p : Pattern) (ha : d115292 p = 1) (hb : d135431 p = 1) : d138172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32375 q ha hb
    | true =>
      simp only [d12361, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32357 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d135431 q = 1) : d138159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32376 q ha hb
    | true =>
      simp only [d12366, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d135431 q = 1) : d138160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d135431 q = 1) : d138170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d135431 q = 1) : d138171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d135431 q = 1) : d138172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32379 (p : Pattern) (ha : d12392 p = 1) (hb : d135431 p = 1) : d138183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12387 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12388 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12389 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6079 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6080 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6081 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12390 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d73 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12259 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12259, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12391 q = 1) (hb : d135431 q = 1) : d138182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12391, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12392 q = 1) (hb : d135431 q = 1) : d138183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12392, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro32380 (p : Pattern) (ha : d12398 p = 1) (hb : d135431 p = 1) : d138189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32379 q ha hb
    | true =>
      simp only [d12393, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32360 q ha hb
    | true =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d135431 q = 1) : d138186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d135431 q = 1) : d138187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d135431 q = 1) : d138188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d135431 q = 1) : d138189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32381 (p : Pattern) (ha : d12418 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32360 q ha hb
    | true =>
      simp only [d12262, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32382 (p : Pattern) (ha : d115302 p = 1) (hb : d135431 p = 1) : d138195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d135431 q = 1) : d138190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32380 q ha hb
    | true =>
      simp only [d12399, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32361 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d135431 q = 1) : d138191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32381 q ha hb
    | true =>
      simp only [d12419, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d135431 q = 1) : d138087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d135431 q = 1) : d138192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d135431 q = 1) : d138193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d135431 q = 1) : d138194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d135431 q = 1) : d138195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32383 (p : Pattern) (ha : d115308 p = 1) (hb : d135431 p = 1) : d138201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d135431 q = 1) : d138108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32364 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d135431 q = 1) : d138109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d135431 q = 1) : d138115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32364 q ha hb
    | true =>
      simp only [d12297, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32365 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d135431 q = 1) : d138116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d135431 q = 1) : d138117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d135431 q = 1) : d138164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32372 q ha hb
    | true =>
      simp only [d115286, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32377 q ha hb
  have h7 (q : Pattern) (ha : d12374 q = 1) (hb : d135431 q = 1) : d138166 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32366 q ha hb
    | true =>
      simp only [d12374, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24109 q ha hb
  have h8 (q : Pattern) (ha : d115287 q = 1) (hb : d135431 q = 1) : d138167 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115288 q = 1) (hb : d135431 q = 1) : d138168 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115288, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115289 q = 1) (hb : d135431 q = 1) : d138169 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115293 q = 1) (hb : d135431 q = 1) : d138173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32378 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24128 q ha hb
  have h13 (q : Pattern) (ha : d115294 q = 1) (hb : d135431 q = 1) : d138174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115294, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115295 q = 1) (hb : d135431 q = 1) : d138175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115295, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115296 q = 1) (hb : d135431 q = 1) : d138176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115296, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115297 q = 1) (hb : d135431 q = 1) : d138177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115297, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115303 q = 1) (hb : d135431 q = 1) : d138196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32382 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24129 q ha hb
  have h19 (q : Pattern) (ha : d115304 q = 1) (hb : d135431 q = 1) : d138197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115304, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115305 q = 1) (hb : d135431 q = 1) : d138198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115305, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115306 q = 1) (hb : d135431 q = 1) : d138199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115306, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115307 q = 1) (hb : d135431 q = 1) : d138200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115307, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115308 q = 1) (hb : d135431 q = 1) : d138201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115308, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32384 (p : Pattern) (ha : d115314 p = 1) (hb : d135431 p = 1) : d138207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24107 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115271 q = 1) (hb : d135431 q = 1) : d138098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115271, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32363 q ha hb
  have h6 (q : Pattern) (ha : d115272 q = 1) (hb : d135431 q = 1) : d138099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115272, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115273 q = 1) (hb : d135431 q = 1) : d138100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115273, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115274 q = 1) (hb : d135431 q = 1) : d138101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115274, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115275 q = 1) (hb : d135431 q = 1) : d138102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115275, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115309 q = 1) (hb : d135431 q = 1) : d138202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115309, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32383 q ha hb
  have h11 (q : Pattern) (ha : d115310 q = 1) (hb : d135431 q = 1) : d138203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115310, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115311 q = 1) (hb : d135431 q = 1) : d138204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115311, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115312 q = 1) (hb : d135431 q = 1) : d138205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115312, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115313 q = 1) (hb : d135431 q = 1) : d138206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115313, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115314 q = 1) (hb : d135431 q = 1) : d138207 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115314, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32385 (p : Pattern) (ha : d12438 p = 1) (hb : d135431 p = 1) : d138135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12313 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12314 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12315 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4818 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4819 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4820 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4821 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12316 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4822 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4822, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12437 q = 1) (hb : d135431 q = 1) : d138134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12437, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12438 q = 1) (hb : d135431 q = 1) : d138135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12438, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32386 (p : Pattern) (ha : d12442 p = 1) (hb : d135431 p = 1) : d138044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4819 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4820 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4821 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4822 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4822, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12441 q = 1) (hb : d135431 q = 1) : d138043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12441, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12442 q = 1) (hb : d135431 q = 1) : d138044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12442, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32387 (p : Pattern) (ha : d12448 p = 1) (hb : d135431 p = 1) : d138141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d135431 q = 1) : d138141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32388 (p : Pattern) (ha : d12452 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32389 (p : Pattern) (ha : d12458 p = 1) (hb : d135431 p = 1) : d138212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32387 q ha hb
    | true =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32388 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d135431 q = 1) : d138212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32390 (p : Pattern) (ha : d12461 p = 1) (hb : d135431 p = 1) : d138157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d135431 q = 1) : d138157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32391 (p : Pattern) (ha : d12462 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32392 (p : Pattern) (ha : d12468 p = 1) (hb : d135431 p = 1) : d138219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32387 q ha hb
    | true =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32388 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32390 q ha hb
    | true =>
      simp only [d12463, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32391 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d135431 q = 1) : d138215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d135431 q = 1) : d138216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d135431 q = 1) : d138217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d135431 q = 1) : d138218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d135431 q = 1) : d138219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32393 (p : Pattern) (ha : d12574 p = 1) (hb : d135431 p = 1) : d138279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32387 q ha hb
    | true =>
      simp only [d12453, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32388 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32388 q ha hb
    | true =>
      simp only [d12569, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d135431 q = 1) : d138279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32394 (p : Pattern) (ha : d12580 p = 1) (hb : d135431 p = 1) : d138114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32388 q ha hb
    | true =>
      simp only [d12569, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32391 q ha hb
    | true =>
      simp only [d12575, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d135431 q = 1) : d138114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32395 (p : Pattern) (ha : d12589 p = 1) (hb : d135431 p = 1) : d138288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32391 q ha hb
    | true =>
      simp only [d12575, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d135431 q = 1) : d138288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32396 (p : Pattern) (ha : d12622 p = 1) (hb : d135431 p = 1) : d138079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6079 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6080 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6081 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6082 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6082, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12621 q = 1) (hb : d135431 q = 1) : d138078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12621, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12622 q = 1) (hb : d135431 q = 1) : d138079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12622, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32397 (p : Pattern) (ha : d12668 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32396 q ha hb
    | true =>
      simp only [d12623, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32398 (p : Pattern) (ha : d12674 p = 1) (hb : d135431 p = 1) : d138323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32397 q ha hb
    | true =>
      simp only [d12669, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d135431 q = 1) : d138319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d135431 q = 1) : d138320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d135431 q = 1) : d138321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d135431 q = 1) : d138322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d135431 q = 1) : d138323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32399 (p : Pattern) (ha : d12473 p = 1) (hb : d135431 p = 1) : d138224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d135431 q = 1) : d138223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d135431 q = 1) : d138224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32400 (p : Pattern) (ha : d12475 p = 1) (hb : d135431 p = 1) : d138119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d135431 q = 1) : d138119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32401 (p : Pattern) (ha : d12482 p = 1) (hb : d135431 p = 1) : d138231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d135431 q = 1) : d138229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d135431 q = 1) : d138230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d135431 q = 1) : d138231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32402 (p : Pattern) (ha : d12485 p = 1) (hb : d135431 p = 1) : d138126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d135431 q = 1) : d138126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32403 (p : Pattern) (ha : d12502 p = 1) (hb : d135431 p = 1) : d161242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12489 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12312 q = 1) (hb : d94753 q = 1) : d12312 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12490 q = 1) (hb : d135431 q = 1) : d138235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d135431, d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12490, d135431, d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12491 q = 1) (hb : d135431 q = 1) : d138236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12492 q = 1) (hb : d135431 q = 1) : d138237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12312 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12496 q = 1) (hb : d94753 q = 1) : d12496 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12497 q = 1) (hb : d135431 q = 1) : d161237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d135431, d161237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12497, d135431, d161237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12498 q = 1) (hb : d135431 q = 1) : d161238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d161238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d161238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12499 q = 1) (hb : d135431 q = 1) : d161239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d161239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d161239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12500 q = 1) (hb : d135431 q = 1) : d161240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d161240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12500, d161240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12313 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12313, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12314 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12315 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4818 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4819 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d4819, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d4820 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4821 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12316 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12316, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12501 q = 1) (hb : d135431 q = 1) : d161241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d161241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12501, d161241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12502 q = 1) (hb : d135431 q = 1) : d161242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d161242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12502, d161242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32404 (p : Pattern) (ha : d12508 p = 1) (hb : d135431 p = 1) : d161248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d135431 q = 1) : d161243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d161243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32403 q ha hb
    | true =>
      simp only [d12503, d161243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d135431 q = 1) : d161244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d161244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d161244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d135431 q = 1) : d161245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d161245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d161245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d135431 q = 1) : d161246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d161246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d161246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d135431 q = 1) : d161247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d161247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d161247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d135431 q = 1) : d161248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d161248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d161248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32405 (p : Pattern) (ha : d12537 p = 1) (hb : d135431 p = 1) : d138252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d135431 q = 1) : d138249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d135431 q = 1) : d138250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d135431 q = 1) : d138251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d135431 q = 1) : d138252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32406 (p : Pattern) (ha : d115319 p = 1) (hb : d135431 p = 1) : d161254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d135431 q = 1) : d138225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32399 q ha hb
    | true =>
      simp only [d12476, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32400 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d135431 q = 1) : d138226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d135431 q = 1) : d138227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d135431 q = 1) : d138228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d135431 q = 1) : d138232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32401 q ha hb
    | true =>
      simp only [d12486, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32402 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d135431 q = 1) : d138233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d135431 q = 1) : d138234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d135431 q = 1) : d161249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d161249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32404 q ha hb
    | true =>
      simp only [d12509, d161249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32387 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d135431 q = 1) : d161250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d161250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d161250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d135431 q = 1) : d138253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32405 q ha hb
    | true =>
      simp only [d12538, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d135431 q = 1) : d138254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d135431 q = 1) : d161251 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d161251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d161251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d135431 q = 1) : d161252 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d161252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d161252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d135431 q = 1) : d161253 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d161253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d161253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115319 q = 1) (hb : d135431 q = 1) : d161254 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d161254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d161254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32407 (p : Pattern) (ha : d12544 p = 1) (hb : d135431 p = 1) : d138259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d135431 q = 1) : d138223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d135431 q = 1) : d138259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32408 (p : Pattern) (ha : d12545 p = 1) (hb : d135431 p = 1) : d138148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d135431 q = 1) : d138148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32409 (p : Pattern) (ha : d12550 p = 1) (hb : d135431 p = 1) : d138264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d135431 q = 1) : d138229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d135431 q = 1) : d138230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d135431 q = 1) : d138264 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32410 (p : Pattern) (ha : d12551 p = 1) (hb : d135431 p = 1) : d138153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32386 q ha hb
    | true =>
      simp only [d12443, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d135431 q = 1) : d138153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32411 (p : Pattern) (ha : d12555 p = 1) (hb : d135431 p = 1) : d161255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d135431 q = 1) : d161243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d161243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32403 q ha hb
    | true =>
      simp only [d12503, d161243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d135431 q = 1) : d161244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d161244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d161244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d135431 q = 1) : d161245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d161245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d161245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d135431 q = 1) : d161246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d161246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d161246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d135431 q = 1) : d161247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d161247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d161247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d135431 q = 1) : d161255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d161255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d161255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32412 (p : Pattern) (ha : d12561 p = 1) (hb : d135431 p = 1) : d138271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32385 q ha hb
    | true =>
      simp only [d12439, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d135431 q = 1) : d138249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d135431 q = 1) : d138250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d135431 q = 1) : d138251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d135431 q = 1) : d138271 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32413 (p : Pattern) (ha : d115324 p = 1) (hb : d135431 p = 1) : d161261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d135431 q = 1) : d138225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32399 q ha hb
    | true =>
      simp only [d12476, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32400 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d135431 q = 1) : d138226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d135431 q = 1) : d138227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d135431 q = 1) : d138228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d135431 q = 1) : d138232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32401 q ha hb
    | true =>
      simp only [d12486, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32402 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d135431 q = 1) : d138233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d135431 q = 1) : d138234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d135431 q = 1) : d161249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d161249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32404 q ha hb
    | true =>
      simp only [d12509, d161249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32387 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d135431 q = 1) : d161250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d161250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d161250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d135431 q = 1) : d138253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32405 q ha hb
    | true =>
      simp only [d12538, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d135431 q = 1) : d138254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d135431 q = 1) : d161251 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d161251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d161251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d135431 q = 1) : d161252 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d161252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d161252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d135431 q = 1) : d161253 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d161253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d161253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d135431 q = 1) : d138260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32407 q ha hb
    | true =>
      simp only [d12546, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32408 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d135431 q = 1) : d138261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d135431 q = 1) : d138262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d135431 q = 1) : d138263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d135431 q = 1) : d138265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32409 q ha hb
    | true =>
      simp only [d12552, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32410 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d135431 q = 1) : d138266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d135431 q = 1) : d138267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d135431 q = 1) : d161256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d161256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32411 q ha hb
    | true =>
      simp only [d12556, d161256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32390 q ha hb
  have h23 (q : Pattern) (ha : d115320 q = 1) (hb : d135431 q = 1) : d161257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d161257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115320, d161257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d135431 q = 1) : d138272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32412 q ha hb
    | true =>
      simp only [d12562, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d135431 q = 1) : d138273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115321 q = 1) (hb : d135431 q = 1) : d161258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d161258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d161258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115322 q = 1) (hb : d135431 q = 1) : d161259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d161259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115322, d161259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115323 q = 1) (hb : d135431 q = 1) : d161260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d161260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115323, d161260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115324 q = 1) (hb : d135431 q = 1) : d161261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d161261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d161261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32414 (p : Pattern) (ha : d115331 p = 1) (hb : d135431 p = 1) : d161268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d135431 q = 1) : d161256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d161256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32411 q ha hb
    | true =>
      simp only [d12556, d161256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32390 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d135431 q = 1) : d161257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d161257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d161257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d135431 q = 1) : d138272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32412 q ha hb
    | true =>
      simp only [d12562, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d135431 q = 1) : d138273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d135431 q = 1) : d161258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d161258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d161258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d135431 q = 1) : d161266 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d161266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d161266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d135431 q = 1) : d161267 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d161267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d161267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d135431 q = 1) : d161268 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d161268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d161268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32415 (p : Pattern) (ha : d12610 p = 1) (hb : d135431 p = 1) : d161279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12386 q = 1) (hb : d94753 q = 1) : d12386 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12596 q = 1) (hb : d135431 q = 1) : d138294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d135431, d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12596, d135431, d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12597 q = 1) (hb : d135431 q = 1) : d138295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12598 q = 1) (hb : d135431 q = 1) : d138296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12386 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12604 q = 1) (hb : d94753 q = 1) : d12604 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12605 q = 1) (hb : d135431 q = 1) : d161274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d135431, d161274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12605, d135431, d161274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12606 q = 1) (hb : d135431 q = 1) : d161275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d161275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d161275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12607 q = 1) (hb : d135431 q = 1) : d161276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d161276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d161276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12608 q = 1) (hb : d135431 q = 1) : d161277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d161277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12608, d161277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12387 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12388 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12389 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d6078 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6079 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6080 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6081 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12390 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12609 q = 1) (hb : d135431 q = 1) : d161278 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d161278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12609, d161278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12610 q = 1) (hb : d135431 q = 1) : d161279 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d161279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12610, d161279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32416 (p : Pattern) (ha : d12614 p = 1) (hb : d135431 p = 1) : d138183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12387 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12387, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12388 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12389 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6079 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6079, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6080 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6081 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12390 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12390, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6082 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6082, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12613 q = 1) (hb : d135431 q = 1) : d138182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12613, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12614 q = 1) (hb : d135431 q = 1) : d138183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12614, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32417 (p : Pattern) (ha : d12620 p = 1) (hb : d135431 p = 1) : d161285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d135431 q = 1) : d161280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d161280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32415 q ha hb
    | true =>
      simp only [d12611, d161280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d135431 q = 1) : d161281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d161281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d161281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32416 q ha hb
    | true =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d135431 q = 1) : d161282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d161282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d161282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d135431 q = 1) : d161283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d161283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d161283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d135431 q = 1) : d161284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d161284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d161284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d135431 q = 1) : d161285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d161285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d161285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32418 (p : Pattern) (ha : d12628 p = 1) (hb : d135431 p = 1) : d138189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32416 q ha hb
    | true =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32396 q ha hb
    | true =>
      simp only [d12623, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d135431 q = 1) : d138186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d135431 q = 1) : d138187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d135431 q = 1) : d138188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d135431 q = 1) : d138189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32419 (p : Pattern) (ha : d12657 p = 1) (hb : d135431 p = 1) : d138311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32416 q ha hb
    | true =>
      simp only [d12615, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d135431 q = 1) : d138308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d135431 q = 1) : d138309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d135431 q = 1) : d138310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d135431 q = 1) : d138311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32420 (p : Pattern) (ha : d115341 p = 1) (hb : d135431 p = 1) : d161291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d135431 q = 1) : d161286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d161286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32417 q ha hb
    | true =>
      simp only [d12629, d161286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32418 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d135431 q = 1) : d161287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d161287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d161287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d135431 q = 1) : d138312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32419 q ha hb
    | true =>
      simp only [d12658, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d135431 q = 1) : d138313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d135431 q = 1) : d161288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d161288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d161288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d135431 q = 1) : d161289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d161289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d161289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d135431 q = 1) : d161290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d161290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d161290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d135431 q = 1) : d161291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d161291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d161291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32421 (p : Pattern) (ha : d115347 p = 1) (hb : d135431 p = 1) : d161297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d135431 q = 1) : d138213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32389 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d135431 q = 1) : d138214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d135431 q = 1) : d138220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32389 q ha hb
    | true =>
      simp only [d12469, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32392 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d135431 q = 1) : d138221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d135431 q = 1) : d138222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d135431 q = 1) : d161262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d161262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32406 q ha hb
    | true =>
      simp only [d115325, d161262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32413 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d135431 q = 1) : d138280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32393 q ha hb
    | true =>
      simp only [d12581, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32394 q ha hb
  have h8 (q : Pattern) (ha : d115326 q = 1) (hb : d135431 q = 1) : d161263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d161263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d161263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115327 q = 1) (hb : d135431 q = 1) : d161264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d161264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d161264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115328 q = 1) (hb : d135431 q = 1) : d161265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d161265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d161265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115332 q = 1) (hb : d135431 q = 1) : d161269 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d161269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d161269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32414 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d135431 q = 1) : d138289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32395 q ha hb
  have h13 (q : Pattern) (ha : d115333 q = 1) (hb : d135431 q = 1) : d161270 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d161270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d161270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115334 q = 1) (hb : d135431 q = 1) : d161271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d161271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d161271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115335 q = 1) (hb : d135431 q = 1) : d161272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d161272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d161272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115336 q = 1) (hb : d135431 q = 1) : d161273 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d161273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d161273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115342 q = 1) (hb : d135431 q = 1) : d161292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d161292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d161292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32420 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d135431 q = 1) : d138324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32398 q ha hb
  have h19 (q : Pattern) (ha : d115343 q = 1) (hb : d135431 q = 1) : d161293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d161293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d161293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115344 q = 1) (hb : d135431 q = 1) : d161294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d161294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d161294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115345 q = 1) (hb : d135431 q = 1) : d161295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d161295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d161295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115346 q = 1) (hb : d135431 q = 1) : d161296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d161296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d161296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115347 q = 1) (hb : d135431 q = 1) : d161297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d161297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d161297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32422 (p : Pattern) (ha : d115353 p = 1) (hb : d135431 p = 1) : d161303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d135431 q = 1) : d161298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d161298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d161298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32421 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d135431 q = 1) : d161299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d161299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d161299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d135431 q = 1) : d161300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d161300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d161300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d135431 q = 1) : d161301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d161301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d161301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d135431 q = 1) : d161302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d161302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d161302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d135431 q = 1) : d161303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d161303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d161303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32423 (p : Pattern) (ha : d12693 p = 1) (hb : d135431 p = 1) : d138346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12489 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4913 q = 1) (hb : d94753 q = 1) : d4913 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12688 q = 1) (hb : d135431 q = 1) : d138337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12688, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12689 q = 1) (hb : d135431 q = 1) : d138338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12690 q = 1) (hb : d135431 q = 1) : d138339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d4913 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4914 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4915 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4916 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12691 q = 1) (hb : d135431 q = 1) : d138343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12691, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4917 q = 1) (hb : d135431 q = 1) : d138344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4917, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12692 q = 1) (hb : d135431 q = 1) : d138345 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12692, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12693 q = 1) (hb : d135431 q = 1) : d138346 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12693, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32424 (p : Pattern) (ha : d12697 p = 1) (hb : d135431 p = 1) : d138350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4914 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4915 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4916 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4917 q = 1) (hb : d135431 q = 1) : d138344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4917, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12696 q = 1) (hb : d135431 q = 1) : d138349 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12696, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12697 q = 1) (hb : d135431 q = 1) : d138350 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12697, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32425 (p : Pattern) (ha : d12703 p = 1) (hb : d135431 p = 1) : d138356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d135431 q = 1) : d138355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d135431 q = 1) : d138356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32426 (p : Pattern) (ha : d12707 p = 1) (hb : d135431 p = 1) : d138360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d135431 q = 1) : d138359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d135431 q = 1) : d138360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32427 (p : Pattern) (ha : d12713 p = 1) (hb : d135431 p = 1) : d138366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32425 q ha hb
    | true =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32426 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d135431 q = 1) : d138366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32428 (p : Pattern) (ha : d12716 p = 1) (hb : d135431 p = 1) : d138369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d135431 q = 1) : d138355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d135431 q = 1) : d138369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32429 (p : Pattern) (ha : d12717 p = 1) (hb : d135431 p = 1) : d138370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d135431 q = 1) : d138359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d135431 q = 1) : d138370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32430 (p : Pattern) (ha : d12723 p = 1) (hb : d135431 p = 1) : d138376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32425 q ha hb
    | true =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32426 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d135431 q = 1) : d138371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32428 q ha hb
    | true =>
      simp only [d12718, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32429 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d135431 q = 1) : d138372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d135431 q = 1) : d138373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d135431 q = 1) : d138374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d135431 q = 1) : d138375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d135431 q = 1) : d138376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32431 (p : Pattern) (ha : d12833 p = 1) (hb : d135431 p = 1) : d138456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32425 q ha hb
    | true =>
      simp only [d12708, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32426 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d135431 q = 1) : d138451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32426 q ha hb
    | true =>
      simp only [d12828, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d135431 q = 1) : d138452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d135431 q = 1) : d138453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d135431 q = 1) : d138454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d135431 q = 1) : d138455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d135431 q = 1) : d138456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32432 (p : Pattern) (ha : d12839 p = 1) (hb : d135431 p = 1) : d138462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d135431 q = 1) : d138451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32426 q ha hb
    | true =>
      simp only [d12828, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d135431 q = 1) : d138452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d135431 q = 1) : d138453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d135431 q = 1) : d138454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d135431 q = 1) : d138455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d135431 q = 1) : d138457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32429 q ha hb
    | true =>
      simp only [d12834, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d135431 q = 1) : d138458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d135431 q = 1) : d138459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d135431 q = 1) : d138460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d135431 q = 1) : d138461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d135431 q = 1) : d138462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32433 (p : Pattern) (ha : d12848 p = 1) (hb : d135431 p = 1) : d138471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d135431 q = 1) : d138457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32429 q ha hb
    | true =>
      simp only [d12834, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d135431 q = 1) : d138458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d135431 q = 1) : d138459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d135431 q = 1) : d138460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d135431 q = 1) : d138461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d135431 q = 1) : d138471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32434 (p : Pattern) (ha : d12885 p = 1) (hb : d135431 p = 1) : d138502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6210 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6211 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6212 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6213 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6214 q = 1) (hb : d135431 q = 1) : d138492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6214, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12884 q = 1) (hb : d135431 q = 1) : d138501 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12884, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12885 q = 1) (hb : d135431 q = 1) : d138502 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12885, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32435 (p : Pattern) (ha : d12935 p = 1) (hb : d135431 p = 1) : d138533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d135431 q = 1) : d138503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32434 q ha hb
    | true =>
      simp only [d12886, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d135431 q = 1) : d138504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d135431 q = 1) : d138530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d135431 q = 1) : d138531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d135431 q = 1) : d138532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d135431 q = 1) : d138533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32436 (p : Pattern) (ha : d12941 p = 1) (hb : d135431 p = 1) : d138539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d135431 q = 1) : d138534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32435 q ha hb
    | true =>
      simp only [d12936, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d135431 q = 1) : d138535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d135431 q = 1) : d138536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d135431 q = 1) : d138537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d135431 q = 1) : d138538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d135431 q = 1) : d138539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32437 (p : Pattern) (ha : d12728 p = 1) (hb : d135431 p = 1) : d138381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d135431 q = 1) : d138380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d135431 q = 1) : d138381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32438 (p : Pattern) (ha : d12730 p = 1) (hb : d135431 p = 1) : d138383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d135431 q = 1) : d138382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d135431 q = 1) : d138383 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32439 (p : Pattern) (ha : d12737 p = 1) (hb : d135431 p = 1) : d138390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d135431 q = 1) : d138388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d135431 q = 1) : d138389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d135431 q = 1) : d138390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32440 (p : Pattern) (ha : d12740 p = 1) (hb : d135431 p = 1) : d138393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d135431 q = 1) : d138391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d135431 q = 1) : d138392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d135431 q = 1) : d138393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32441 (p : Pattern) (ha : d12757 p = 1) (hb : d135431 p = 1) : d161310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12489 q = 1) (hb : d94753 q = 1) : d12489 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12745 q = 1) (hb : d135431 q = 1) : d138397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d135431, d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12745, d135431, d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12746 q = 1) (hb : d135431 q = 1) : d138398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12747 q = 1) (hb : d135431 q = 1) : d138399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12489 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12751 q = 1) (hb : d94753 q = 1) : d12751 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12752 q = 1) (hb : d135431 q = 1) : d161305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d135431, d161305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12752, d135431, d161305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12753 q = 1) (hb : d135431 q = 1) : d161306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d161306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d161306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12754 q = 1) (hb : d135431 q = 1) : d161307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d161307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d161307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12755 q = 1) (hb : d135431 q = 1) : d161308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d161308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12755, d161308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4913 q = 1) (hb : d94753 q = 1) : d4913 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12688 q = 1) (hb : d135431 q = 1) : d138337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12688, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12689 q = 1) (hb : d135431 q = 1) : d138338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12690 q = 1) (hb : d135431 q = 1) : d138339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d4913 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4914 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d4914, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d4915 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4916 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12691 q = 1) (hb : d135431 q = 1) : d138343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12691, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12756 q = 1) (hb : d135431 q = 1) : d161309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d161309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12756, d161309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12757 q = 1) (hb : d135431 q = 1) : d161310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d161310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12757, d161310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32442 (p : Pattern) (ha : d12763 p = 1) (hb : d135431 p = 1) : d161316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d135431 q = 1) : d161311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d161311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32441 q ha hb
    | true =>
      simp only [d12758, d161311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d135431 q = 1) : d161312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d161312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d161312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d135431 q = 1) : d161313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d161313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d161313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d135431 q = 1) : d161314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d161314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d161314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d135431 q = 1) : d161315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d161315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d161315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d135431 q = 1) : d161316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d161316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d161316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32443 (p : Pattern) (ha : d12796 p = 1) (hb : d135431 p = 1) : d161322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d135431 q = 1) : d161319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d161319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d161319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d135431 q = 1) : d161320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d161320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d161320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d135431 q = 1) : d161321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d161321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d161321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d135431 q = 1) : d161322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d161322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d161322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32444 (p : Pattern) (ha : d115359 p = 1) (hb : d135431 p = 1) : d161328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d135431 q = 1) : d138384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32437 q ha hb
    | true =>
      simp only [d12731, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32438 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d135431 q = 1) : d138385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d135431 q = 1) : d138386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d135431 q = 1) : d138387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d135431 q = 1) : d138394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32439 q ha hb
    | true =>
      simp only [d12741, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32440 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d135431 q = 1) : d138395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d135431 q = 1) : d138396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d135431 q = 1) : d161317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d161317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32442 q ha hb
    | true =>
      simp only [d12764, d161317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32425 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d135431 q = 1) : d161318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d161318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d161318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d135431 q = 1) : d161323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d161323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32443 q ha hb
    | true =>
      simp only [d12797, d161323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d135431 q = 1) : d161324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d161324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d161324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d135431 q = 1) : d161325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d161325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d161325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d135431 q = 1) : d161326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d161326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d161326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d135431 q = 1) : d161327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d161327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d161327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115359 q = 1) (hb : d135431 q = 1) : d161328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d161328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d161328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32445 (p : Pattern) (ha : d12803 p = 1) (hb : d135431 p = 1) : d138429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d135431 q = 1) : d138380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d135431 q = 1) : d138429 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32446 (p : Pattern) (ha : d12804 p = 1) (hb : d135431 p = 1) : d138430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d135431 q = 1) : d138382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d135431 q = 1) : d138430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32447 (p : Pattern) (ha : d12809 p = 1) (hb : d135431 p = 1) : d138435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d135431 q = 1) : d138388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d135431 q = 1) : d138389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d135431 q = 1) : d138435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32448 (p : Pattern) (ha : d12810 p = 1) (hb : d135431 p = 1) : d138436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32424 q ha hb
    | true =>
      simp only [d12698, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d135431 q = 1) : d138391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d135431 q = 1) : d138392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d135431 q = 1) : d138436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32449 (p : Pattern) (ha : d12814 p = 1) (hb : d135431 p = 1) : d161329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d135431 q = 1) : d161311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d161311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32441 q ha hb
    | true =>
      simp only [d12758, d161311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d135431 q = 1) : d161312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d161312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d161312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d135431 q = 1) : d161313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d161313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d161313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d135431 q = 1) : d161314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d161314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d161314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d135431 q = 1) : d161315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d161315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d161315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d135431 q = 1) : d161329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d161329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d161329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32450 (p : Pattern) (ha : d12820 p = 1) (hb : d135431 p = 1) : d161332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32423 q ha hb
    | true =>
      simp only [d12694, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d135431 q = 1) : d161319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d161319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d161319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d135431 q = 1) : d161320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d161320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d161320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d135431 q = 1) : d161321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d161321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d161321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d135431 q = 1) : d161332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d161332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d161332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32451 (p : Pattern) (ha : d115364 p = 1) (hb : d135431 p = 1) : d161338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d135431 q = 1) : d138384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32437 q ha hb
    | true =>
      simp only [d12731, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32438 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d135431 q = 1) : d138385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d135431 q = 1) : d138386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d135431 q = 1) : d138387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d135431 q = 1) : d138394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32439 q ha hb
    | true =>
      simp only [d12741, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32440 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d135431 q = 1) : d138395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d135431 q = 1) : d138396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d135431 q = 1) : d161317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d161317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32442 q ha hb
    | true =>
      simp only [d12764, d161317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32425 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d135431 q = 1) : d161318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d161318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d161318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d135431 q = 1) : d161323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d161323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32443 q ha hb
    | true =>
      simp only [d12797, d161323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d135431 q = 1) : d161324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d161324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d161324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d135431 q = 1) : d161325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d161325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d161325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d135431 q = 1) : d161326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d161326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d161326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d135431 q = 1) : d161327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d161327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d161327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d135431 q = 1) : d138431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32445 q ha hb
    | true =>
      simp only [d12805, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32446 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d135431 q = 1) : d138432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d135431 q = 1) : d138433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d135431 q = 1) : d138434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d135431 q = 1) : d138437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32447 q ha hb
    | true =>
      simp only [d12811, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32448 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d135431 q = 1) : d138438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d135431 q = 1) : d138439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d135431 q = 1) : d161330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d161330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32449 q ha hb
    | true =>
      simp only [d12815, d161330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32428 q ha hb
  have h23 (q : Pattern) (ha : d115360 q = 1) (hb : d135431 q = 1) : d161331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d161331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115360, d161331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d135431 q = 1) : d161333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d161333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32450 q ha hb
    | true =>
      simp only [d12821, d161333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d135431 q = 1) : d161334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d161334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d161334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115361 q = 1) (hb : d135431 q = 1) : d161335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d161335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d161335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115362 q = 1) (hb : d135431 q = 1) : d161336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d161336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115362, d161336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115363 q = 1) (hb : d135431 q = 1) : d161337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d161337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115363, d161337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115364 q = 1) (hb : d135431 q = 1) : d161338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d161338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d161338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32452 (p : Pattern) (ha : d115371 p = 1) (hb : d135431 p = 1) : d161345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d135431 q = 1) : d161330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d161330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32449 q ha hb
    | true =>
      simp only [d12815, d161330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32428 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d135431 q = 1) : d161331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d161331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d161331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d135431 q = 1) : d161333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d161333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32450 q ha hb
    | true =>
      simp only [d12821, d161333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d135431 q = 1) : d161334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d161334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d161334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d135431 q = 1) : d161335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d161335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d161335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d135431 q = 1) : d161343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d161343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d161343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d135431 q = 1) : d161344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d161344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d161344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d135431 q = 1) : d161345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d161345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d161345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32453 (p : Pattern) (ha : d12873 p = 1) (hb : d135431 p = 1) : d161356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12595 q = 1) (hb : d94753 q = 1) : d12595 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12855 q = 1) (hb : d135431 q = 1) : d138477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d135431, d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12855, d135431, d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12856 q = 1) (hb : d135431 q = 1) : d138478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12857 q = 1) (hb : d135431 q = 1) : d138479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12863 q = 1) (hb : d94753 q = 1) : d12863 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12864 q = 1) (hb : d135431 q = 1) : d161351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d135431, d161351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12864, d135431, d161351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12865 q = 1) (hb : d135431 q = 1) : d161352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d161352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d161352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12866 q = 1) (hb : d135431 q = 1) : d161353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d161353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d161353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12867 q = 1) (hb : d135431 q = 1) : d161354 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d161354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12867, d161354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6210 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12868 q = 1) (hb : d135431 q = 1) : d138480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12868, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12869 q = 1) (hb : d135431 q = 1) : d138481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12870 q = 1) (hb : d135431 q = 1) : d138482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d6210 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6211 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6212 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6213 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12871 q = 1) (hb : d135431 q = 1) : d138487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12871, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12872 q = 1) (hb : d135431 q = 1) : d161355 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d161355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12872, d161355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12873 q = 1) (hb : d135431 q = 1) : d161356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d161356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12873, d161356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32454 (p : Pattern) (ha : d12877 p = 1) (hb : d135431 p = 1) : d138494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6210 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12868 q = 1) (hb : d135431 q = 1) : d138480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12868, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12869 q = 1) (hb : d135431 q = 1) : d138481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12870 q = 1) (hb : d135431 q = 1) : d138482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6210 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6211 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6211, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6212 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6213 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12871 q = 1) (hb : d135431 q = 1) : d138487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12871, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6214 q = 1) (hb : d135431 q = 1) : d138492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6214, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12876 q = 1) (hb : d135431 q = 1) : d138493 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12876, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12877 q = 1) (hb : d135431 q = 1) : d138494 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12877, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32455 (p : Pattern) (ha : d12883 p = 1) (hb : d135431 p = 1) : d161362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d135431 q = 1) : d161357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d161357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32453 q ha hb
    | true =>
      simp only [d12874, d161357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d135431 q = 1) : d161358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d161358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d161358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d135431 q = 1) : d138495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32454 q ha hb
    | true =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d135431 q = 1) : d138496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d135431 q = 1) : d161359 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d161359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d161359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d135431 q = 1) : d161360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d161360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d161360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d135431 q = 1) : d161361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d161361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d161361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d135431 q = 1) : d161362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d161362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d161362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32456 (p : Pattern) (ha : d12891 p = 1) (hb : d135431 p = 1) : d138508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d135431 q = 1) : d138495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32454 q ha hb
    | true =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d135431 q = 1) : d138496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d135431 q = 1) : d138503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32434 q ha hb
    | true =>
      simp only [d12886, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d135431 q = 1) : d138504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d135431 q = 1) : d138505 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d135431 q = 1) : d138506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d135431 q = 1) : d138507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d135431 q = 1) : d138508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32457 (p : Pattern) (ha : d12924 p = 1) (hb : d135431 p = 1) : d161368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d135431 q = 1) : d138495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32454 q ha hb
    | true =>
      simp only [d12878, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d135431 q = 1) : d138496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d135431 q = 1) : d161365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d161365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d161365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d135431 q = 1) : d161366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d161366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d161366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d135431 q = 1) : d161367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d161367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d161367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d135431 q = 1) : d161368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d161368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d161368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32458 (p : Pattern) (ha : d115381 p = 1) (hb : d135431 p = 1) : d161374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d135431 q = 1) : d161363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d161363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32455 q ha hb
    | true =>
      simp only [d12892, d161363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32456 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d135431 q = 1) : d161364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d161364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d161364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d135431 q = 1) : d161369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d161369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32457 q ha hb
    | true =>
      simp only [d12925, d161369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d135431 q = 1) : d161370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d161370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d161370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d135431 q = 1) : d161371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d161371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d161371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d135431 q = 1) : d161372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d161372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d161372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d135431 q = 1) : d161373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d161373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d161373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d135431 q = 1) : d161374 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d161374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d161374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32459 (p : Pattern) (ha : d115387 p = 1) (hb : d135431 p = 1) : d161380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d135431 q = 1) : d138367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32427 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d135431 q = 1) : d138368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d135431 q = 1) : d138377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32427 q ha hb
    | true =>
      simp only [d12724, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32430 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d135431 q = 1) : d138378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d135431 q = 1) : d138379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d135431 q = 1) : d161339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d161339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32444 q ha hb
    | true =>
      simp only [d115365, d161339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32451 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d135431 q = 1) : d138463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32431 q ha hb
    | true =>
      simp only [d12840, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32432 q ha hb
  have h8 (q : Pattern) (ha : d115366 q = 1) (hb : d135431 q = 1) : d161340 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d161340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d161340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115367 q = 1) (hb : d135431 q = 1) : d161341 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d161341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d161341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115368 q = 1) (hb : d135431 q = 1) : d161342 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d161342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d161342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115372 q = 1) (hb : d135431 q = 1) : d161346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d161346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d161346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32452 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d135431 q = 1) : d138472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32433 q ha hb
  have h13 (q : Pattern) (ha : d115373 q = 1) (hb : d135431 q = 1) : d161347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d161347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d161347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115374 q = 1) (hb : d135431 q = 1) : d161348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d161348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d161348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115375 q = 1) (hb : d135431 q = 1) : d161349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d161349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d161349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115376 q = 1) (hb : d135431 q = 1) : d161350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d161350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d161350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115382 q = 1) (hb : d135431 q = 1) : d161375 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d161375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d161375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32458 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d135431 q = 1) : d138540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32436 q ha hb
  have h19 (q : Pattern) (ha : d115383 q = 1) (hb : d135431 q = 1) : d161376 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d161376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d161376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115384 q = 1) (hb : d135431 q = 1) : d161377 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d161377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d161377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115385 q = 1) (hb : d135431 q = 1) : d161378 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d161378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d161378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115386 q = 1) (hb : d135431 q = 1) : d161379 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d161379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d161379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115387 q = 1) (hb : d135431 q = 1) : d161380 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d161380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d161380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32460 (p : Pattern) (ha : d115393 p = 1) (hb : d135431 p = 1) : d161386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d135431 q = 1) : d161381 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d161381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d161381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32459 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d135431 q = 1) : d161382 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d161382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d161382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d135431 q = 1) : d161383 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d161383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d161383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d135431 q = 1) : d161384 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d161384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d161384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d135431 q = 1) : d161385 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d161385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d161385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d135431 q = 1) : d161386 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d161386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d161386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32461 (p : Pattern) (ha : d12967 p = 1) (hb : d135431 p = 1) : d161394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12957 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12958 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12959 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5023 q = 1) (hb : d94753 q = 1) : d5023 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5024 q = 1) (hb : d135431 q = 1) : d161389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5025 q = 1) (hb : d135431 q = 1) : d161390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5026 q = 1) (hb : d135431 q = 1) : d161391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12960 q = 1) (hb : d135431 q = 1) : d161392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12961 q = 1) (hb : d94753 q = 1) : d12961 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12962 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12962, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12963 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12964 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12965 q = 1) (hb : d135431 q = 1) : d138561 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12965, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d12966 q = 1) (hb : d135431 q = 1) : d161393 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d161393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12966, d161393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12967 q = 1) (hb : d135431 q = 1) : d161394 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d161394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d12967, d161394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32462 (p : Pattern) (ha : d12971 p = 1) (hb : d135431 p = 1) : d138567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5009 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12961 q = 1) (hb : d94753 q = 1) : d12961 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12962 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12962, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12963 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12964 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12965 q = 1) (hb : d135431 q = 1) : d138561 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12965, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12970 q = 1) (hb : d135431 q = 1) : d138566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12970, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12971 q = 1) (hb : d135431 q = 1) : d138567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12971, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32463 (p : Pattern) (ha : d12977 p = 1) (hb : d135431 p = 1) : d161400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d135431 q = 1) : d161398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d135431 q = 1) : d161399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d161399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d161399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d135431 q = 1) : d161400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d161400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d161400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32464 (p : Pattern) (ha : d12981 p = 1) (hb : d135431 p = 1) : d138577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d135431 q = 1) : d138576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d135431 q = 1) : d138577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32465 (p : Pattern) (ha : d12987 p = 1) (hb : d135431 p = 1) : d161406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d135431 q = 1) : d161401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d161401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32463 q ha hb
    | true =>
      simp only [d12982, d161401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32464 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d135431 q = 1) : d161402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d161402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d161402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d135431 q = 1) : d161403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d161403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d161403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d135431 q = 1) : d161404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d161404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d161404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d135431 q = 1) : d161405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d161405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d161405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d135431 q = 1) : d161406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d161406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d161406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32466 (p : Pattern) (ha : d12990 p = 1) (hb : d135431 p = 1) : d161409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d135431 q = 1) : d161398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d135431 q = 1) : d161399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d161399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d161399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d135431 q = 1) : d161409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d161409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d161409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32467 (p : Pattern) (ha : d12991 p = 1) (hb : d135431 p = 1) : d138587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d135431 q = 1) : d138576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d135431 q = 1) : d138587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32468 (p : Pattern) (ha : d12997 p = 1) (hb : d135431 p = 1) : d161415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d135431 q = 1) : d161401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d161401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32463 q ha hb
    | true =>
      simp only [d12982, d161401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32464 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d135431 q = 1) : d161402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d161402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d161402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d135431 q = 1) : d161403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d161403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d161403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d135431 q = 1) : d161404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d161404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d161404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d135431 q = 1) : d161405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d161405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d161405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d135431 q = 1) : d161410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d161410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32466 q ha hb
    | true =>
      simp only [d12992, d161410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32467 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d135431 q = 1) : d161411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d161411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d161411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d135431 q = 1) : d161412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d161412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d161412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d135431 q = 1) : d161413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d161413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d161413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d135431 q = 1) : d161414 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d161414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d161414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d135431 q = 1) : d161415 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d161415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d161415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32469 (p : Pattern) (ha : d13040 p = 1) (hb : d135431 p = 1) : d161441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12957 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12958 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12959 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5023 q = 1) (hb : d94753 q = 1) : d5023 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5024 q = 1) (hb : d135431 q = 1) : d161389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5025 q = 1) (hb : d135431 q = 1) : d161390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5026 q = 1) (hb : d135431 q = 1) : d161391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12960 q = 1) (hb : d135431 q = 1) : d161392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5027 q = 1) (hb : d135431 q = 1) : d161439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d161439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5027, d161439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13039 q = 1) (hb : d135431 q = 1) : d161440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d161440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13039, d161440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13040 q = 1) (hb : d135431 q = 1) : d161441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d161441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13040, d161441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32470 (p : Pattern) (ha : d13050 p = 1) (hb : d135431 p = 1) : d161451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d135431 q = 1) : d161442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32469 q ha hb
    | true =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d135431 q = 1) : d161443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d135431 q = 1) : d161448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d161448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d161448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d135431 q = 1) : d161449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d161449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d161449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d135431 q = 1) : d161450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d161450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d161450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d135431 q = 1) : d161451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d161451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d161451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32471 (p : Pattern) (ha : d13134 p = 1) (hb : d135431 p = 1) : d161490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d135431 q = 1) : d161485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d161485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32470 q ha hb
    | true =>
      simp only [d13124, d161485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32464 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d135431 q = 1) : d161486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d161486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d161486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d135431 q = 1) : d161487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d161487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d161487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d135431 q = 1) : d161488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d161488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d161488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d135431 q = 1) : d161489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d161489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d161489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d135431 q = 1) : d138668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32464 q ha hb
    | true =>
      simp only [d13129, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d135431 q = 1) : d138669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d135431 q = 1) : d138670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d135431 q = 1) : d138671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d135431 q = 1) : d138672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d135431 q = 1) : d161490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d161490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d161490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32472 (p : Pattern) (ha : d13140 p = 1) (hb : d135431 p = 1) : d138679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d135431 q = 1) : d138668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32464 q ha hb
    | true =>
      simp only [d13129, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d135431 q = 1) : d138669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d135431 q = 1) : d138670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d135431 q = 1) : d138671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d135431 q = 1) : d138672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d135431 q = 1) : d138674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32467 q ha hb
    | true =>
      simp only [d13135, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d135431 q = 1) : d138675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d135431 q = 1) : d138676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d135431 q = 1) : d138677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d135431 q = 1) : d138678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d135431 q = 1) : d138679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32473 (p : Pattern) (ha : d13149 p = 1) (hb : d135431 p = 1) : d138688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d135431 q = 1) : d138674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32467 q ha hb
    | true =>
      simp only [d13135, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d135431 q = 1) : d138675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d135431 q = 1) : d138676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d135431 q = 1) : d138677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d135431 q = 1) : d138678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d135431 q = 1) : d138688 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32474 (p : Pattern) (ha : d13196 p = 1) (hb : d135431 p = 1) : d138719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13190 q = 1) (hb : d94753 q = 1) : d13190 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13191 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13191, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13192 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13193 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13194 q = 1) (hb : d135431 q = 1) : d138709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13194, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13195 q = 1) (hb : d135431 q = 1) : d138718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13195, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13196 q = 1) (hb : d135431 q = 1) : d138719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13196, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32475 (p : Pattern) (ha : d13260 p = 1) (hb : d135431 p = 1) : d138750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d135431 q = 1) : d138720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32474 q ha hb
    | true =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d135431 q = 1) : d138721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d135431 q = 1) : d138747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d135431 q = 1) : d138748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d135431 q = 1) : d138749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d135431 q = 1) : d138750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32476 (p : Pattern) (ha : d13266 p = 1) (hb : d135431 p = 1) : d138756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d135431 q = 1) : d138751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32475 q ha hb
    | true =>
      simp only [d13261, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d135431 q = 1) : d138752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d135431 q = 1) : d138753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d135431 q = 1) : d138754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d135431 q = 1) : d138755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d135431 q = 1) : d138756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32477 (p : Pattern) (ha : d13002 p = 1) (hb : d135431 p = 1) : d161420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d135431 q = 1) : d161398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d135431 q = 1) : d161419 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d161419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d161419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d135431 q = 1) : d161420 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d161420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d161420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32478 (p : Pattern) (ha : d13004 p = 1) (hb : d135431 p = 1) : d138600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d135431 q = 1) : d138599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d135431 q = 1) : d138600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32479 (p : Pattern) (ha : d13011 p = 1) (hb : d135431 p = 1) : d161427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d135431 q = 1) : d161425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d161425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d161425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d135431 q = 1) : d161426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d161426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d161426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d135431 q = 1) : d161427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d161427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d161427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32480 (p : Pattern) (ha : d13014 p = 1) (hb : d135431 p = 1) : d138610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d135431 q = 1) : d138608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d135431 q = 1) : d138609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d135431 q = 1) : d138610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32481 (p : Pattern) (ha : d13036 p = 1) (hb : d135431 p = 1) : d161436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12956 q = 1) (hb : d94753 q = 1) : d12956 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13019 q = 1) (hb : d135431 q = 1) : d138614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d135431, d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13019, d135431, d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13020 q = 1) (hb : d135431 q = 1) : d138615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13021 q = 1) (hb : d135431 q = 1) : d138616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12956 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13030 q = 1) (hb : d94753 q = 1) : d13030 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13031 q = 1) (hb : d135431 q = 1) : d161431 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d135431, d161431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13031, d135431, d161431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13032 q = 1) (hb : d135431 q = 1) : d161432 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d161432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d161432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13033 q = 1) (hb : d135431 q = 1) : d161433 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d161433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d161433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13034 q = 1) (hb : d135431 q = 1) : d161434 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d161434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13034, d161434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12957 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d12957, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12958 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12959 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d5009 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5023 q = 1) (hb : d94753 q = 1) : d5023 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5024 q = 1) (hb : d135431 q = 1) : d161389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d5024, d135431, d161389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5025 q = 1) (hb : d135431 q = 1) : d161390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d161390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5026 q = 1) (hb : d135431 q = 1) : d161391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d161391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12960 q = 1) (hb : d135431 q = 1) : d161392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12960, d161392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13035 q = 1) (hb : d135431 q = 1) : d161435 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d161435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13035, d161435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13036 q = 1) (hb : d135431 q = 1) : d161436 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d161436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13036, d161436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32482 (p : Pattern) (ha : d13046 p = 1) (hb : d135431 p = 1) : d161447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d135431 q = 1) : d161437 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d161437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32481 q ha hb
    | true =>
      simp only [d13037, d161437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d135431 q = 1) : d161438 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d161438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d161438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d135431 q = 1) : d161442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32469 q ha hb
    | true =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d135431 q = 1) : d161443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d135431 q = 1) : d161444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d161444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d161444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d135431 q = 1) : d161445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d161445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d161445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d135431 q = 1) : d161446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d161446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d161446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d135431 q = 1) : d161447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d161447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d161447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32483 (p : Pattern) (ha : d13091 p = 1) (hb : d135431 p = 1) : d161457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d135431 q = 1) : d161454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d161454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d161454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d135431 q = 1) : d161455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d161455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d161455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d135431 q = 1) : d161456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d161456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d161456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d135431 q = 1) : d161457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d161457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d161457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32484 (p : Pattern) (ha : d115400 p = 1) (hb : d135431 p = 1) : d161463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d135431 q = 1) : d161421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d161421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32477 q ha hb
    | true =>
      simp only [d13005, d161421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32478 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d135431 q = 1) : d161422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d161422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d161422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d135431 q = 1) : d161423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d161423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d161423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d135431 q = 1) : d161424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d161424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d161424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d135431 q = 1) : d161428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d161428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32479 q ha hb
    | true =>
      simp only [d13015, d161428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32480 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d135431 q = 1) : d161429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d161429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d161429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d135431 q = 1) : d161430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d161430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d161430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d135431 q = 1) : d161452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d161452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32482 q ha hb
    | true =>
      simp only [d13051, d161452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32470 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d135431 q = 1) : d161453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d161453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d161453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d135431 q = 1) : d161458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d161458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32483 q ha hb
    | true =>
      simp only [d13092, d161458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d135431 q = 1) : d161459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d161459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d161459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d135431 q = 1) : d161460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d161460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d161460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d135431 q = 1) : d161461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d161461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d161461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d135431 q = 1) : d161462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d161462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d161462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d135431 q = 1) : d161463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d161463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d161463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32485 (p : Pattern) (ha : d13098 p = 1) (hb : d135431 p = 1) : d161464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d135431 q = 1) : d161398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d161398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d135431 q = 1) : d161419 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d161419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d161419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d135431 q = 1) : d161464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d161464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d161464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32486 (p : Pattern) (ha : d13099 p = 1) (hb : d135431 p = 1) : d138647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d135431 q = 1) : d138599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d135431 q = 1) : d138647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d138647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32487 (p : Pattern) (ha : d13104 p = 1) (hb : d135431 p = 1) : d161469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d135431 q = 1) : d161397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d161397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d135431 q = 1) : d161425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d161425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d161425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d135431 q = 1) : d161426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d161426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d161426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d135431 q = 1) : d161469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d161469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d161469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32488 (p : Pattern) (ha : d13105 p = 1) (hb : d135431 p = 1) : d138653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d135431 q = 1) : d138608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d135431 q = 1) : d138609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d135431 q = 1) : d138653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d138653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32489 (p : Pattern) (ha : d13109 p = 1) (hb : d135431 p = 1) : d161473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d135431 q = 1) : d161437 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d161437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32481 q ha hb
    | true =>
      simp only [d13037, d161437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d135431 q = 1) : d161438 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d161438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d161438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d135431 q = 1) : d161442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32469 q ha hb
    | true =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d135431 q = 1) : d161443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d135431 q = 1) : d161444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d161444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d161444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d135431 q = 1) : d161445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d161445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d161445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d135431 q = 1) : d161446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d161446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d161446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d135431 q = 1) : d161473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d161473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d161473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32490 (p : Pattern) (ha : d13110 p = 1) (hb : d135431 p = 1) : d161474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d135431 q = 1) : d161442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32469 q ha hb
    | true =>
      simp only [d13041, d161442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d135431 q = 1) : d161443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d161443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32462 q ha hb
    | true =>
      simp only [d12972, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d135431 q = 1) : d161448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d161448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d161448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d135431 q = 1) : d161449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d161449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d161449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d135431 q = 1) : d161450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d161450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d161450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d135431 q = 1) : d161474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d161474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d161474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32491 (p : Pattern) (ha : d13116 p = 1) (hb : d135431 p = 1) : d161477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d135431 q = 1) : d161395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32461 q ha hb
    | true =>
      simp only [d12968, d161395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d135431 q = 1) : d161396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d161396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d135431 q = 1) : d161454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d161454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d161454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d135431 q = 1) : d161455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d161455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d161455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d135431 q = 1) : d161456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d161456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d161456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d135431 q = 1) : d161477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d161477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d161477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro32492 (p : Pattern) (ha : d115405 p = 1) (hb : d135431 p = 1) : d161483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d135431 q = 1) : d161421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d161421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32477 q ha hb
    | true =>
      simp only [d13005, d161421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32478 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d135431 q = 1) : d161422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d161422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d161422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d135431 q = 1) : d161423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d161423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d161423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d135431 q = 1) : d161424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d161424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d161424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d135431 q = 1) : d161428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d161428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32479 q ha hb
    | true =>
      simp only [d13015, d161428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32480 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d135431 q = 1) : d161429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d161429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d161429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d135431 q = 1) : d161430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d161430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d161430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d135431 q = 1) : d161452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d161452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32482 q ha hb
    | true =>
      simp only [d13051, d161452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32470 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d135431 q = 1) : d161453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d161453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d161453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d135431 q = 1) : d161458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d161458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32483 q ha hb
    | true =>
      simp only [d13092, d161458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d135431 q = 1) : d161459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d161459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d161459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d135431 q = 1) : d161460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d161460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d161460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d135431 q = 1) : d161461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d161461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d161461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d135431 q = 1) : d161462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d161462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d161462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d135431 q = 1) : d161465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d161465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32485 q ha hb
    | true =>
      simp only [d13100, d161465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32486 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d135431 q = 1) : d161466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d161466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d161466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d135431 q = 1) : d161467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d161467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d161467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d135431 q = 1) : d161468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d161468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d161468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d135431 q = 1) : d161470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d161470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32487 q ha hb
    | true =>
      simp only [d13106, d161470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32488 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d135431 q = 1) : d161471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d161471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d161471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d135431 q = 1) : d161472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d161472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d161472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d135431 q = 1) : d161475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d161475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32489 q ha hb
    | true =>
      simp only [d13111, d161475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32490 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d135431 q = 1) : d161476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d161476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d161476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d135431 q = 1) : d161478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d161478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32491 q ha hb
    | true =>
      simp only [d13117, d161478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d135431 q = 1) : d161479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d161479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d161479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d135431 q = 1) : d161480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d161480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d161480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d135431 q = 1) : d161481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d161481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d161481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d135431 q = 1) : d161482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d161482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d161482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d135431 q = 1) : d161483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d161483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d161483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro32493 (p : Pattern) (ha : d115412 p = 1) (hb : d135431 p = 1) : d161497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d135431 q = 1) : d161475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d161475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32489 q ha hb
    | true =>
      simp only [d13111, d161475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32490 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d135431 q = 1) : d161476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d161476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d161476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d135431 q = 1) : d161478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d161478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32491 q ha hb
    | true =>
      simp only [d13117, d161478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d135431 q = 1) : d161479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d161479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d161479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d135431 q = 1) : d161480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d161480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d161480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d135431 q = 1) : d161495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d161495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d161495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d135431 q = 1) : d161496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d161496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d161496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d135431 q = 1) : d161497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d161497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d161497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32494 (p : Pattern) (ha : d13179 p = 1) (hb : d135431 p = 1) : d161512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13156 q = 1) (hb : d94753 q = 1) : d13156 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13157 q = 1) (hb : d135431 q = 1) : d138694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d135431, d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13157, d135431, d138694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13158 q = 1) (hb : d135431 q = 1) : d138695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d138695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13159 q = 1) (hb : d135431 q = 1) : d138696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d138696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13156 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13169 q = 1) (hb : d94753 q = 1) : d13169 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13170 q = 1) (hb : d135431 q = 1) : d161503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d135431, d161503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13170, d135431, d161503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13171 q = 1) (hb : d135431 q = 1) : d161504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d161504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d161504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13172 q = 1) (hb : d135431 q = 1) : d161505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d161505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d161505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13173 q = 1) (hb : d135431 q = 1) : d161506 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d161506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13173, d161506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13174 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13175 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13176 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d6349 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6355 q = 1) (hb : d94753 q = 1) : d6355 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6356 q = 1) (hb : d135431 q = 1) : d161507 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6357 q = 1) (hb : d135431 q = 1) : d161508 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6358 q = 1) (hb : d135431 q = 1) : d161509 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13177 q = 1) (hb : d135431 q = 1) : d161510 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13178 q = 1) (hb : d135431 q = 1) : d161511 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d161511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13178, d161511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13179 q = 1) (hb : d135431 q = 1) : d161512 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d161512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13179, d161512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h23 p ha hb
theorem andIntro32495 (p : Pattern) (ha : d13183 p = 1) (hb : d135431 p = 1) : d161517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13174 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13175 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13176 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6355 q = 1) (hb : d94753 q = 1) : d6355 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6356 q = 1) (hb : d135431 q = 1) : d161507 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6357 q = 1) (hb : d135431 q = 1) : d161508 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6358 q = 1) (hb : d135431 q = 1) : d161509 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13177 q = 1) (hb : d135431 q = 1) : d161510 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6359 q = 1) (hb : d135431 q = 1) : d161515 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d161515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6359, d161515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13182 q = 1) (hb : d135431 q = 1) : d161516 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d161516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13182, d161516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13183 q = 1) (hb : d135431 q = 1) : d161517 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d161517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13183, d161517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro32496 (p : Pattern) (ha : d13189 p = 1) (hb : d135431 p = 1) : d161523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d135431 q = 1) : d161513 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d161513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32494 q ha hb
    | true =>
      simp only [d13180, d161513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d135431 q = 1) : d161514 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d161514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d161514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d135431 q = 1) : d161518 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d161518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32495 q ha hb
    | true =>
      simp only [d13184, d161518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d135431 q = 1) : d161519 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d161519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d161519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d135431 q = 1) : d161520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d161520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d161520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d135431 q = 1) : d161521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d161521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d161521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d135431 q = 1) : d161522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d161522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d161522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d135431 q = 1) : d161523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d161523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d161523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32497 (p : Pattern) (ha : d13202 p = 1) (hb : d135431 p = 1) : d161527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d135431 q = 1) : d161518 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d161518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32495 q ha hb
    | true =>
      simp only [d13184, d161518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d135431 q = 1) : d161519 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d161519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d161519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d135431 q = 1) : d138720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32474 q ha hb
    | true =>
      simp only [d13197, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d135431 q = 1) : d138721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d135431 q = 1) : d161524 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d161524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d161524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d135431 q = 1) : d161525 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d161525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d161525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d135431 q = 1) : d161526 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d161526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d161526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d135431 q = 1) : d161527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d161527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d161527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro32498 (p : Pattern) (ha : d13243 p = 1) (hb : d135431 p = 1) : d161531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13174 q = 1) (hb : d135431 q = 1) : d138697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13174, d135431, d138697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13175 q = 1) (hb : d135431 q = 1) : d138698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d138698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13176 q = 1) (hb : d135431 q = 1) : d138699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d138699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6355 q = 1) (hb : d94753 q = 1) : d6355 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6356 q = 1) (hb : d135431 q = 1) : d161507 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d6356, d135431, d161507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6357 q = 1) (hb : d135431 q = 1) : d161508 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d161508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6358 q = 1) (hb : d135431 q = 1) : d161509 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d161509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13177 q = 1) (hb : d135431 q = 1) : d161510 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13177, d161510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13190 q = 1) (hb : d94753 q = 1) : d13190 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13191 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d13191, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13192 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13193 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13194 q = 1) (hb : d135431 q = 1) : d138709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13194, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d13242 q = 1) (hb : d135431 q = 1) : d161530 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d161530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13242, d161530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13243 q = 1) (hb : d135431 q = 1) : d161531 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d161531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13243, d161531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro32499 (p : Pattern) (ha : d13249 p = 1) (hb : d135431 p = 1) : d161537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d135431 q = 1) : d161532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d161532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32498 q ha hb
    | true =>
      simp only [d13244, d161532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d135431 q = 1) : d161533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d161533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d161533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d135431 q = 1) : d161534 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d161534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d161534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d135431 q = 1) : d161535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d161535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d161535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d135431 q = 1) : d161536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d161536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d161536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d135431 q = 1) : d161537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d161537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d161537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
