import NetHack.Soko22Hazard87.AndIntroBlocks0341
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro85500 (p : Pattern) (ha : d261986 p = 1) (hb : d312503 p = 1) : d265826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34898 q = 1) (hb : d261986 q = 1) : d265172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34898, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85025 q ha hb
    | true =>
      simp only [d34898, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85028 q ha hb
  have h2 (q : Pattern) (ha : d34899 q = 1) (hb : d261986 q = 1) : d265173 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34899, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34899, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312484 q = 1) : d265807 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312484, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312484, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312485 q = 1) : d265808 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312485, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312485, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312487 q = 1) : d265810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312487, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312487, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85498 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312488 q = 1) : d265811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312488, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312488, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261986 q = 1) (hb : d312489 q = 1) : d265812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312489, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312489, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261986 q = 1) (hb : d312490 q = 1) : d265813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312490, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312490, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261986 q = 1) (hb : d312491 q = 1) : d265814 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312491, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312491, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261986 q = 1) (hb : d312498 q = 1) : d265821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312498, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312498, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85499 q ha hb
  have h11 (q : Pattern) (ha : d261986 q = 1) (hb : d312499 q = 1) : d265822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312499, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312499, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261986 q = 1) (hb : d312500 q = 1) : d265823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312500, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312500, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261986 q = 1) (hb : d312501 q = 1) : d265824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312501, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312501, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261986 q = 1) (hb : d312502 q = 1) : d265825 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312502, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312502, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261986 q = 1) (hb : d312503 q = 1) : d265826 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312503, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312503, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85501 (p : Pattern) (ha : d261986 p = 1) (hb : d312509 p = 1) : d265832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312504 q = 1) : d265827 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312504, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312504, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85500 q ha hb
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312505 q = 1) : d265828 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312505, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312505, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312506 q = 1) : d265829 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312506, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312506, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312507 q = 1) : d265830 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312507, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312507, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312508 q = 1) : d265831 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312508, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312508, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312509 q = 1) : d265832 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312509, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312509, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85502 (p : Pattern) (ha : d261986 p = 1) (hb : d312516 p = 1) : d265839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35475 q = 1) (hb : d261986 q = 1) : d265445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d35475, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85094 q ha hb
    | true =>
      simp only [d35475, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85095 q ha hb
  have h2 (q : Pattern) (ha : d35476 q = 1) (hb : d261986 q = 1) : d265446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d35476, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35476, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35477 q = 1) (hb : d261986 q = 1) : d265447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d35477, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35477, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35478 q = 1) (hb : d261986 q = 1) : d265448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d35478, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35478, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35479 q = 1) (hb : d261986 q = 1) : d265449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d35479, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35479, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312516 q = 1) : d265839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312516, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312516, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro85503 (p : Pattern) (ha : d261986 p = 1) (hb : d312523 p = 1) : d265585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35771 q = 1) (hb : d261986 q = 1) : d265570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35771, d265570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85132 q ha hb
    | true =>
      simp only [d35771, d265570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85102 q ha hb
  have h2 (q : Pattern) (ha : d35772 q = 1) (hb : d261986 q = 1) : d265571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35772, d265571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35772, d265571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35773 q = 1) (hb : d261986 q = 1) : d265572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35773, d265572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35773, d265572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35780 q = 1) (hb : d261986 q = 1) : d265575 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35780, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85102 q ha hb
    | true =>
      simp only [d35780, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85134 q ha hb
  have h5 (q : Pattern) (ha : d35781 q = 1) (hb : d261986 q = 1) : d265576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35781, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35781, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35782 q = 1) (hb : d261986 q = 1) : d265577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35782, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35782, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d35783 q = 1) (hb : d261986 q = 1) : d265578 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35783, d265578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35783, d265578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d35799 q = 1) (hb : d261986 q = 1) : d265575 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35799, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85102 q ha hb
    | true =>
      simp only [d35799, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85103 q ha hb
  have h9 (q : Pattern) (ha : d35800 q = 1) (hb : d261986 q = 1) : d265576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35800, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35800, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d35801 q = 1) (hb : d261986 q = 1) : d265577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35801, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35801, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d35802 q = 1) (hb : d261986 q = 1) : d265583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35802, d265583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d35802, d265583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d261986 q = 1) (hb : d312522 q = 1) : d265584 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312522, d265584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312522, d265584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d261986 q = 1) (hb : d312523 q = 1) : d265585 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312523, d265585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312523, d265585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro85504 (p : Pattern) (ha : d261986 p = 1) (hb : d312529 p = 1) : d265599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312524 q = 1) : d265586 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312524, d265586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85503 q ha hb
    | true =>
      simp only [d312524, d265586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312525 q = 1) : d265587 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312525, d265587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312525, d265587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35805 q = 1) (hb : d261986 q = 1) : d265594 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d35805, d265594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85104 q ha hb
    | true =>
      simp only [d35805, d265594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35806 q = 1) (hb : d261986 q = 1) : d265595 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d35806, d265595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35806, d265595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312526 q = 1) : d265596 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312526, d265596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312526, d265596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312527 q = 1) : d265597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312527, d265597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312527, d265597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261986 q = 1) (hb : d312528 q = 1) : d265598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312528, d265598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312528, d265598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261986 q = 1) (hb : d312529 q = 1) : d265599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312529, d265599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312529, d265599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro85505 (p : Pattern) (ha : d261986 p = 1) (hb : d312535 p = 1) : d10411 p = 1 := by
  have h0 (q : Pattern) (ha : d2058 q = 1) (hb : d261985 q = 1) : d2058 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2042 q = 1) (hb : d261985 q = 1) : d2042 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312530 q = 1) : d2043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d312530, d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83255 q hb ha
    | true =>
      simp only [d312530, d2043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312531 q = 1) : d2059 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d312531, d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312531, d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312532 q = 1) : d2076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d261986, d312532, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d261986, d312532, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10408 q = 1) (hb : d261986 q = 1) : d10408 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d261986 q = 1) (hb : d312533 q = 1) : d10409 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d312533, d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312533, d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d261986 q = 1) (hb : d312534 q = 1) : d10410 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d312534, d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312534, d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d261986 q = 1) (hb : d312535 q = 1) : d10411 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d312535, d10411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312535, d10411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h10 p ha hb
theorem andIntro85506 (p : Pattern) (ha : d261986 p = 1) (hb : d312541 p = 1) : d265574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35765 q = 1) (hb : d261986 q = 1) : d265559 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35765, d265559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35765, d265559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85084 q ha hb
  have h2 (q : Pattern) (ha : d35417 q = 1) (hb : d261986 q = 1) : d265402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35417, d265402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85084 q ha hb
    | true =>
      simp only [d35417, d265402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35766 q = 1) (hb : d261986 q = 1) : d265560 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35766, d265560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35766, d265560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35418 q = 1) (hb : d261986 q = 1) : d265403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35418, d265403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35418, d265403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35767 q = 1) (hb : d261986 q = 1) : d265561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35767, d265561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35767, d265561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35768 q = 1) (hb : d261986 q = 1) : d265562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35768, d265562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35768, d265562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35797 q = 1) (hb : d261986 q = 1) : d265568 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d35797, d265568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35797, d265568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15791 q = 1) (hb : d261986 q = 1) : d15791 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d261986 q = 1) (hb : d312536 q = 1) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d312536, d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85505 q ha hb
    | true =>
      simp only [d312536, d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d261986 q = 1) (hb : d312537 q = 1) : d10414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d312537, d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312537, d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d261986 q = 1) (hb : d312538 q = 1) : d15792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d312538, d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d312538, d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d261986 q = 1) (hb : d312539 q = 1) : d15793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d312539, d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312539, d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261986 q = 1) (hb : d312540 q = 1) : d15794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d312540, d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312540, d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261986 q = 1) (hb : d312541 q = 1) : d265574 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d312541, d265574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312541, d265574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro85507 (p : Pattern) (ha : d261986 p = 1) (hb : d312547 p = 1) : d265593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312542 q = 1) : d265575 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d312542, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85102 q hb ha
    | true =>
      simp only [d312542, d265575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85506 q ha hb
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312543 q = 1) : d265576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d312543, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312543, d265576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312544 q = 1) : d265577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d312544, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312544, d265577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312545 q = 1) : d265583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d312545, d265583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312545, d265583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312546 q = 1) : d265592 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312546, d265592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312546, d265592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312547 q = 1) : d265593 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312547, d265593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312547, d265593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85508 (p : Pattern) (ha : d261986 p = 1) (hb : d312553 p = 1) : d265631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312548 q = 1) : d265594 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312548, d265594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85507 q ha hb
    | true =>
      simp only [d312548, d265594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312549 q = 1) : d265595 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312549, d265595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312549, d265595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312550 q = 1) : d265628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312550, d265628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312550, d265628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312551 q = 1) : d265629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312551, d265629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312551, d265629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312552 q = 1) : d265630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312552, d265630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312552, d265630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312553 q = 1) : d265631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312553, d265631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312553, d265631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85509 (p : Pattern) (ha : d261986 p = 1) (hb : d312559 p = 1) : d265850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312554 q = 1) : d265845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312554, d265845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85504 q ha hb
    | true =>
      simp only [d312554, d265845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85508 q ha hb
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312555 q = 1) : d265846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312555, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312555, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312556 q = 1) : d265847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312556, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312556, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312557 q = 1) : d265848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312557, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312557, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312558 q = 1) : d265849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312558, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312558, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312559 q = 1) : d265850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312559, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312559, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85510 (p : Pattern) (ha : d261986 p = 1) (hb : d312565 p = 1) : d265856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35481 q = 1) (hb : d261986 q = 1) : d265451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d35481, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85093 q ha hb
    | true =>
      simp only [d35481, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85096 q ha hb
  have h2 (q : Pattern) (ha : d35482 q = 1) (hb : d261986 q = 1) : d265452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d35482, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35482, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312514 q = 1) : d265837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312514, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312514, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312515 q = 1) : d265838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312515, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312515, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312517 q = 1) : d265840 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312517, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312517, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85502 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312518 q = 1) : d265841 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312518, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312518, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261986 q = 1) (hb : d312519 q = 1) : d265842 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312519, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312519, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261986 q = 1) (hb : d312520 q = 1) : d265843 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312520, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312520, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261986 q = 1) (hb : d312521 q = 1) : d265844 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312521, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312521, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261986 q = 1) (hb : d312560 q = 1) : d265851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312560, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312560, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85509 q ha hb
  have h11 (q : Pattern) (ha : d261986 q = 1) (hb : d312561 q = 1) : d265852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312561, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312561, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261986 q = 1) (hb : d312562 q = 1) : d265853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312562, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312562, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261986 q = 1) (hb : d312563 q = 1) : d265854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312563, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312563, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261986 q = 1) (hb : d312564 q = 1) : d265855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312564, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312564, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261986 q = 1) (hb : d312565 q = 1) : d265856 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312565, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312565, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85511 (p : Pattern) (ha : d261986 p = 1) (hb : d312571 p = 1) : d265862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312566 q = 1) : d265857 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312566, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312566, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85510 q ha hb
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312567 q = 1) : d265858 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312567, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312567, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312568 q = 1) : d265859 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312568, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312568, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312569 q = 1) : d265860 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312569, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312569, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312570 q = 1) : d265861 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312570, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312570, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312571 q = 1) : d265862 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312571, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312571, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85512 (p : Pattern) (ha : d261986 p = 1) (hb : d312577 p = 1) : d265868 p = 1 := by
  have h0 (q : Pattern) (ha : d261986 q = 1) (hb : d312426 q = 1) : d265749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312426, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85485 q ha hb
    | true =>
      simp only [d312426, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85489 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312453 q = 1) : d265776 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312453, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312453, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85493 q ha hb
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312454 q = 1) : d265777 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312454, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312454, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312481 q = 1) : d265804 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312481, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312481, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85497 q ha hb
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312482 q = 1) : d265805 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312482, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312482, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312483 q = 1) : d265806 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312483, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312483, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d261986 q = 1) (hb : d312510 q = 1) : d265833 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312510, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312510, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85501 q ha hb
  have h8 (q : Pattern) (ha : d261986 q = 1) (hb : d312511 q = 1) : d265834 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312511, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312511, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d261986 q = 1) (hb : d312512 q = 1) : d265835 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312512, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312512, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261986 q = 1) (hb : d312513 q = 1) : d265836 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312513, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312513, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d261986 q = 1) (hb : d312572 q = 1) : d265863 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312572, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312572, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85511 q ha hb
  have h12 (q : Pattern) (ha : d261986 q = 1) (hb : d312573 q = 1) : d265864 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312573, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312573, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d261986 q = 1) (hb : d312574 q = 1) : d265865 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312574, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312574, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d261986 q = 1) (hb : d312575 q = 1) : d265866 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312575, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312575, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d261986 q = 1) (hb : d312576 q = 1) : d265867 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d312576, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312576, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d261986 q = 1) (hb : d312577 q = 1) : d265868 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d312577, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312577, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro85513 (p : Pattern) (ha : d261986 p = 1) (hb : d312583 p = 1) : d265874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312578 q = 1) : d265869 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d312578, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85512 q ha hb
    | true =>
      simp only [d312578, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312579 q = 1) : d265870 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d312579, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312579, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312580 q = 1) : d265871 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d312580, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312580, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312581 q = 1) : d265872 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d312581, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312581, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312582 q = 1) : d265873 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d312582, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312582, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312583 q = 1) : d265874 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d312583, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312583, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85514 (p : Pattern) (ha : d261986 p = 1) (hb : d312589 p = 1) : d265880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312584 q = 1) : d265875 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d312584, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85513 q ha hb
    | true =>
      simp only [d312584, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312585 q = 1) : d265876 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d312585, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312585, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312586 q = 1) : d265877 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d312586, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312586, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312587 q = 1) : d265878 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d312587, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312587, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312588 q = 1) : d265879 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d312588, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312588, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312589 q = 1) : d265880 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d312589, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312589, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85515 (p : Pattern) (ha : d261986 p = 1) (hb : d312595 p = 1) : d265886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312590 q = 1) : d265881 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d312590, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85514 q ha hb
    | true =>
      simp only [d312590, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312591 q = 1) : d265882 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d312591, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312591, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312592 q = 1) : d265883 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d312592, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312592, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312593 q = 1) : d265884 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d312593, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312593, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312594 q = 1) : d265885 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d312594, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312594, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312595 q = 1) : d265886 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d312595, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312595, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85516 (p : Pattern) (ha : d261986 p = 1) (hb : d312601 p = 1) : d265892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312596 q = 1) : d265887 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d312596, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85515 q ha hb
    | true =>
      simp only [d312596, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312597 q = 1) : d265888 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d312597, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312597, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312598 q = 1) : d265889 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d312598, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312598, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312599 q = 1) : d265890 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d312599, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312599, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312600 q = 1) : d265891 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d312600, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312600, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312601 q = 1) : d265892 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d312601, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312601, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85517 (p : Pattern) (ha : d261986 p = 1) (hb : d312607 p = 1) : d265898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312602 q = 1) : d265893 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d312602, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85516 q ha hb
    | true =>
      simp only [d312602, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312603 q = 1) : d265894 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d312603, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312603, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312604 q = 1) : d265895 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d312604, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312604, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312605 q = 1) : d265896 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d312605, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312605, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312606 q = 1) : d265897 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d312606, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312606, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312607 q = 1) : d265898 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d312607, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312607, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85518 (p : Pattern) (ha : d261986 p = 1) (hb : d312613 p = 1) : d265904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312608 q = 1) : d265899 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d312608, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85517 q ha hb
    | true =>
      simp only [d312608, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312609 q = 1) : d265900 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d312609, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312609, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312610 q = 1) : d265901 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d312610, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312610, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312611 q = 1) : d265902 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d312611, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312611, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312612 q = 1) : d265903 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d312612, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312612, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312613 q = 1) : d265904 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d312613, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312613, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85519 (p : Pattern) (ha : d261986 p = 1) (hb : d312619 p = 1) : d265910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261986 q = 1) (hb : d312614 q = 1) : d265905 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d312614, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85518 q ha hb
    | true =>
      simp only [d312614, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261986 q = 1) (hb : d312615 q = 1) : d265906 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d312615, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312615, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261986 q = 1) (hb : d312616 q = 1) : d265907 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d312616, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312616, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261986 q = 1) (hb : d312617 q = 1) : d265908 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d312617, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312617, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261986 q = 1) (hb : d312618 q = 1) : d265909 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d312618, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312618, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261986 q = 1) (hb : d312619 q = 1) : d265910 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d312619, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312619, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85520 (p : Pattern) (ha : d198617 p = 1) (hb : d264133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198489 q = 1) (hb : d264069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d264069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85158 q ha hb
    | true =>
      simp only [d198489, d264069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d198607 q = 1) (hb : d264129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198607, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198614 q = 1) (hb : d264130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198614, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198615 q = 1) (hb : d264131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198615, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198616 q = 1) (hb : d264132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198616, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198617 q = 1) (hb : d264133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198617, d264133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198617, d264133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85521 (p : Pattern) (ha : d198636 p = 1) (hb : d264140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198489 q = 1) (hb : d264069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d264069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85158 q ha hb
    | true =>
      simp only [d198489, d264069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d198607 q = 1) (hb : d264129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198607, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198614 q = 1) (hb : d264130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198614, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198615 q = 1) (hb : d264131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198615, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198616 q = 1) (hb : d264132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198616, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198622 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198626 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198496 q = 1) (hb : d264076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d264076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85160 q ha hb
    | true =>
      simp only [d198496, d264076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d198629 q = 1) (hb : d264136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198629, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198633 q = 1) (hb : d264137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198633, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198634 q = 1) (hb : d264138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198634, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198634, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198635 q = 1) (hb : d264139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198635, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198635, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198636 q = 1) (hb : d264140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198636, d264140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198636, d264140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85522 (p : Pattern) (ha : d198645 p = 1) (hb : d265700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198496 q = 1) (hb : d264076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d264076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85160 q ha hb
    | true =>
      simp only [d198496, d264076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d198629 q = 1) (hb : d264136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198629, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198633 q = 1) (hb : d264137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198633, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198643 q = 1) (hb : d264138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198643, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198643, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198644 q = 1) (hb : d264139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198644, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198644, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198645 q = 1) (hb : d265700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198645, d265700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198645, d265700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85523 (p : Pattern) (ha : d198685 p = 1) (hb : d265710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198532 q = 1) (hb : d264112 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198532, d264112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85165 q ha hb
    | true =>
      simp only [d198532, d264112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d198675 q = 1) (hb : d265706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198675, d265706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198675, d265706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198682 q = 1) (hb : d265707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198682, d265707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198682, d265707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198683 q = 1) (hb : d265708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198683, d265708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198683, d265708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198684 q = 1) (hb : d265709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198684, d265709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198684, d265709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198685 q = 1) (hb : d265710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198685, d265710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198685, d265710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85524 (p : Pattern) (ha : d198691 p = 1) (hb : d265716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198637 q = 1) (hb : d264141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198637, d264141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85520 q ha hb
    | true =>
      simp only [d198637, d264141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85521 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198640 q = 1) (hb : d264142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198640, d264142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198640, d264142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198641 q = 1) (hb : d265698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198641, d265698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198641, d265698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198642 q = 1) (hb : d265699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198642, d265699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198642, d265699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198646 q = 1) (hb : d265701 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198646, d265701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198646, d265701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85522 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198647 q = 1) (hb : d265702 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198647, d265702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198647, d265702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198648 q = 1) (hb : d265703 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198648, d265703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198648, d265703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198649 q = 1) (hb : d265704 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198649, d265704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198649, d265704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198650 q = 1) (hb : d265705 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198650, d265705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198650, d265705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198686 q = 1) (hb : d265711 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198686, d265711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198686, d265711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85523 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198687 q = 1) (hb : d265712 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198687, d265712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198687, d265712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198688 q = 1) (hb : d265713 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198688, d265713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198688, d265713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198689 q = 1) (hb : d265714 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198689, d265714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198689, d265714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198690 q = 1) (hb : d265715 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198690, d265715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198690, d265715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198691 q = 1) (hb : d265716 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198691, d265716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198691, d265716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85525 (p : Pattern) (ha : d198697 p = 1) (hb : d265722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d198544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47793 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d198545 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d198546 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d198547 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d198548 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198692 q = 1) (hb : d265717 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198692, d265717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198692, d265717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85524 q ha hb
  have h8 (q : Pattern) (ha : d198693 q = 1) (hb : d265718 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198693, d265718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198693, d265718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198694 q = 1) (hb : d265719 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198694, d265719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198694, d265719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198695 q = 1) (hb : d265720 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198695, d265720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198695, d265720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198696 q = 1) (hb : d265721 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198696, d265721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198696, d265721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198697 q = 1) (hb : d265722 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198697, d265722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d198697, d265722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro85526 (p : Pattern) (ha : d198808 p = 1) (hb : d264303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198715 q = 1) (hb : d264298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d264298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85196 q ha hb
    | true =>
      simp only [d198715, d264298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85197 q ha hb
  have h5 (q : Pattern) (ha : d198798 q = 1) (hb : d264299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198798, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198805 q = 1) (hb : d264300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198805, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198806 q = 1) (hb : d264301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198806, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198807 q = 1) (hb : d264302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198807, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198808 q = 1) (hb : d264303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198808, d264303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198808, d264303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85527 (p : Pattern) (ha : d198829 p = 1) (hb : d264313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198715 q = 1) (hb : d264298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d264298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85196 q ha hb
    | true =>
      simp only [d198715, d264298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85197 q ha hb
  have h4 (q : Pattern) (ha : d198798 q = 1) (hb : d264299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198798, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198805 q = 1) (hb : d264300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198805, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198806 q = 1) (hb : d264301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198806, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198807 q = 1) (hb : d264302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198807, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198814 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198819 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198725 q = 1) (hb : d264308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d264308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85199 q ha hb
    | true =>
      simp only [d198725, d264308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85200 q ha hb
  have h13 (q : Pattern) (ha : d198822 q = 1) (hb : d264309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198822, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198826 q = 1) (hb : d264310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198826, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198827 q = 1) (hb : d264311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198827, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198827, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198828 q = 1) (hb : d264312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198828, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198828, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198829 q = 1) (hb : d264313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198829, d264313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198829, d264313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85528 (p : Pattern) (ha : d198849 p = 1) (hb : d265725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198725 q = 1) (hb : d264308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d264308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85199 q ha hb
    | true =>
      simp only [d198725, d264308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85200 q ha hb
  have h3 (q : Pattern) (ha : d198822 q = 1) (hb : d264309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198822, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198826 q = 1) (hb : d264310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198826, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198847 q = 1) (hb : d264311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198847, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198847, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198848 q = 1) (hb : d264312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198848, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198848, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198849 q = 1) (hb : d265725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198849, d265725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198849, d265725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85529 (p : Pattern) (ha : d198917 p = 1) (hb : d265736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198906 q = 1) (hb : d265731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198906, d265731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85234 q ha hb
    | true =>
      simp only [d198906, d265731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85237 q ha hb
  have h3 (q : Pattern) (ha : d198907 q = 1) (hb : d265732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198907, d265732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198907, d265732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198914 q = 1) (hb : d265733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198914, d265733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198914, d265733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198915 q = 1) (hb : d265734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198915, d265734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198915, d265734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198916 q = 1) (hb : d265735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198916, d265735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198916, d265735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198917 q = 1) (hb : d265736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198917, d265736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198917, d265736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85530 (p : Pattern) (ha : d198930 p = 1) (hb : d265742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198830 q = 1) (hb : d264314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198830, d264314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85526 q ha hb
    | true =>
      simp only [d198830, d264314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85527 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198844 q = 1) (hb : d264315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198844, d264315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198844, d264315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198845 q = 1) (hb : d265723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198845, d265723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198845, d265723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198846 q = 1) (hb : d265724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198846, d265724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198846, d265724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198850 q = 1) (hb : d265726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198850, d265726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198850, d265726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85528 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d198852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198853 q = 1) (hb : d265727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198853, d265727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198853, d265727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198854 q = 1) (hb : d265728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198854, d265728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198854, d265728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198855 q = 1) (hb : d265729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198855, d265729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198855, d265729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198856 q = 1) (hb : d265730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198856, d265730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198856, d265730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198918 q = 1) (hb : d265737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198918, d265737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198918, d265737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85529 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198925 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198926 q = 1) (hb : d265738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198926, d265738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198926, d265738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198927 q = 1) (hb : d265739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198927, d265739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198927, d265739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198928 q = 1) (hb : d265740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198928, d265740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198928, d265740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198929 q = 1) (hb : d265741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198929, d265741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198929, d265741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198930 q = 1) (hb : d265742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198930, d265742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198930, d265742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85531 (p : Pattern) (ha : d198936 p = 1) (hb : d265748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198931 q = 1) (hb : d265743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198931, d265743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198931, d265743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85530 q ha hb
  have h2 (q : Pattern) (ha : d198932 q = 1) (hb : d265744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198932, d265744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198932, d265744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198933 q = 1) (hb : d265745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198933, d265745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198933, d265745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198934 q = 1) (hb : d265746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198934, d265746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198934, d265746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198935 q = 1) (hb : d265747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198935, d265747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198935, d265747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198936 q = 1) (hb : d265748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198936, d265748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198936, d265748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85532 (p : Pattern) (ha : d199065 p = 1) (hb : d264556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198973 q = 1) (hb : d264551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d264551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85247 q ha hb
    | true =>
      simp only [d198973, d264551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85248 q ha hb
  have h5 (q : Pattern) (ha : d199055 q = 1) (hb : d264552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199055, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199062 q = 1) (hb : d264553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199062, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199063 q = 1) (hb : d264554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199063, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199064 q = 1) (hb : d264555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199064, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199065 q = 1) (hb : d264556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199065, d264556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199065, d264556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85533 (p : Pattern) (ha : d199086 p = 1) (hb : d264566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198973 q = 1) (hb : d264551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d264551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85247 q ha hb
    | true =>
      simp only [d198973, d264551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85248 q ha hb
  have h4 (q : Pattern) (ha : d199055 q = 1) (hb : d264552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199055, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199062 q = 1) (hb : d264553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199062, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199063 q = 1) (hb : d264554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199063, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199064 q = 1) (hb : d264555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199064, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199071 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199076 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198983 q = 1) (hb : d264561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d264561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85250 q ha hb
    | true =>
      simp only [d198983, d264561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85251 q ha hb
  have h13 (q : Pattern) (ha : d199079 q = 1) (hb : d264562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199079, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199083 q = 1) (hb : d264563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199083, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199084 q = 1) (hb : d264564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199084, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199084, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199085 q = 1) (hb : d264565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199085, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199085, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199086 q = 1) (hb : d264566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199086, d264566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199086, d264566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85534 (p : Pattern) (ha : d199106 p = 1) (hb : d265752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198983 q = 1) (hb : d264561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d264561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85250 q ha hb
    | true =>
      simp only [d198983, d264561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85251 q ha hb
  have h3 (q : Pattern) (ha : d199079 q = 1) (hb : d264562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199079, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199083 q = 1) (hb : d264563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199083, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199104 q = 1) (hb : d264564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199104, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199104, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199105 q = 1) (hb : d264565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199105, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199105, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199106 q = 1) (hb : d265752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199106, d265752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199106, d265752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85535 (p : Pattern) (ha : d199191 p = 1) (hb : d265763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199180 q = 1) (hb : d265758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199180, d265758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85287 q ha hb
    | true =>
      simp only [d199180, d265758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85290 q ha hb
  have h3 (q : Pattern) (ha : d199181 q = 1) (hb : d265759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199181, d265759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199181, d265759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199188 q = 1) (hb : d265760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199188, d265760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199188, d265760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199189 q = 1) (hb : d265761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199189, d265761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199189, d265761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199190 q = 1) (hb : d265762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199190, d265762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199190, d265762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199191 q = 1) (hb : d265763 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199191, d265763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199191, d265763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85536 (p : Pattern) (ha : d199204 p = 1) (hb : d265769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199087 q = 1) (hb : d264567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199087, d264567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85532 q ha hb
    | true =>
      simp only [d199087, d264567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85533 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199101 q = 1) (hb : d264568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199101, d264568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199101, d264568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199102 q = 1) (hb : d265750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199102, d265750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199102, d265750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199103 q = 1) (hb : d265751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199103, d265751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199103, d265751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199107 q = 1) (hb : d265753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199107, d265753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199107, d265753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85534 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199109 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199110 q = 1) (hb : d265754 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199110, d265754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199110, d265754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199111 q = 1) (hb : d265755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199111, d265755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199111, d265755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199112 q = 1) (hb : d265756 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199112, d265756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199112, d265756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199113 q = 1) (hb : d265757 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199113, d265757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199113, d265757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199192 q = 1) (hb : d265764 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199192, d265764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199192, d265764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85535 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199200 q = 1) (hb : d265765 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199200, d265765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199200, d265765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199201 q = 1) (hb : d265766 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199201, d265766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199201, d265766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199202 q = 1) (hb : d265767 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199202, d265767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199202, d265767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199203 q = 1) (hb : d265768 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199203, d265768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199203, d265768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199204 q = 1) (hb : d265769 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199204, d265769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199204, d265769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85537 (p : Pattern) (ha : d199210 p = 1) (hb : d265775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199205 q = 1) (hb : d265770 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199205, d265770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199205, d265770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85536 q ha hb
  have h2 (q : Pattern) (ha : d199206 q = 1) (hb : d265771 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199206, d265771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199206, d265771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199207 q = 1) (hb : d265772 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199207, d265772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199207, d265772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199208 q = 1) (hb : d265773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199208, d265773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199208, d265773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199209 q = 1) (hb : d265774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199209, d265774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199209, d265774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199210 q = 1) (hb : d265775 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199210, d265775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199210, d265775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85538 (p : Pattern) (ha : d199376 p = 1) (hb : d264852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199283 q = 1) (hb : d264847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d264847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85304 q ha hb
    | true =>
      simp only [d199283, d264847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85305 q ha hb
  have h5 (q : Pattern) (ha : d199357 q = 1) (hb : d264848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199357, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199373 q = 1) (hb : d264849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199373, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199374 q = 1) (hb : d264850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199374, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199375 q = 1) (hb : d264851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199375, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199376 q = 1) (hb : d264852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199376, d264852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199376, d264852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85539 (p : Pattern) (ha : d199397 p = 1) (hb : d264862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199283 q = 1) (hb : d264847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d264847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85304 q ha hb
    | true =>
      simp only [d199283, d264847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85305 q ha hb
  have h4 (q : Pattern) (ha : d199357 q = 1) (hb : d264848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199357, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199373 q = 1) (hb : d264849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199373, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199374 q = 1) (hb : d264850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199374, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199375 q = 1) (hb : d264851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199375, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199293 q = 1) (hb : d264857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d264857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85307 q ha hb
    | true =>
      simp only [d199293, d264857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85308 q ha hb
  have h13 (q : Pattern) (ha : d199390 q = 1) (hb : d264858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199390, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199394 q = 1) (hb : d264859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199394, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199395 q = 1) (hb : d264860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199395, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199395, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199396 q = 1) (hb : d264861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199396, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199396, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199397 q = 1) (hb : d264862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199397, d264862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199397, d264862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85540 (p : Pattern) (ha : d199417 p = 1) (hb : d265780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199293 q = 1) (hb : d264857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d264857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85307 q ha hb
    | true =>
      simp only [d199293, d264857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85308 q ha hb
  have h3 (q : Pattern) (ha : d199390 q = 1) (hb : d264858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199390, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199394 q = 1) (hb : d264859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199394, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199415 q = 1) (hb : d264860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199415, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199415, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199416 q = 1) (hb : d264861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199416, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199416, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199417 q = 1) (hb : d265780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199417, d265780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199417, d265780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85541 (p : Pattern) (ha : d199528 p = 1) (hb : d265791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199508 q = 1) (hb : d265786 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199508, d265786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85344 q ha hb
    | true =>
      simp only [d199508, d265786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85349 q ha hb
  have h3 (q : Pattern) (ha : d199509 q = 1) (hb : d265787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199509, d265787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199509, d265787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199525 q = 1) (hb : d265788 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199525, d265788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199525, d265788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199526 q = 1) (hb : d265789 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199526, d265789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199526, d265789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199527 q = 1) (hb : d265790 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199527, d265790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199527, d265790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199528 q = 1) (hb : d265791 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199528, d265791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199528, d265791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85542 (p : Pattern) (ha : d199541 p = 1) (hb : d265797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199398 q = 1) (hb : d264863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199398, d264863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85538 q ha hb
    | true =>
      simp only [d199398, d264863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85539 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199412 q = 1) (hb : d264864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199412, d264864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199412, d264864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199413 q = 1) (hb : d265778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199413, d265778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199413, d265778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199414 q = 1) (hb : d265779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199414, d265779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199414, d265779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199418 q = 1) (hb : d265781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199418, d265781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199418, d265781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85540 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199421 q = 1) (hb : d265782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199421, d265782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199421, d265782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199422 q = 1) (hb : d265783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199422, d265783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199422, d265783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199423 q = 1) (hb : d265784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199423, d265784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199423, d265784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199424 q = 1) (hb : d265785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199424, d265785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199424, d265785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199529 q = 1) (hb : d265792 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199529, d265792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199529, d265792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85541 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199536 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199537 q = 1) (hb : d265793 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199537, d265793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199537, d265793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199538 q = 1) (hb : d265794 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199538, d265794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199538, d265794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199539 q = 1) (hb : d265795 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199539, d265795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199539, d265795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199540 q = 1) (hb : d265796 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199540, d265796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199540, d265796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199541 q = 1) (hb : d265797 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199541, d265797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199541, d265797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85543 (p : Pattern) (ha : d199547 p = 1) (hb : d265803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199542 q = 1) (hb : d265798 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199542, d265798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199542, d265798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85542 q ha hb
  have h2 (q : Pattern) (ha : d199543 q = 1) (hb : d265799 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199543, d265799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199543, d265799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199544 q = 1) (hb : d265800 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199544, d265800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199544, d265800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199545 q = 1) (hb : d265801 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199545, d265801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199545, d265801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199546 q = 1) (hb : d265802 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199546, d265802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199546, d265802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199547 q = 1) (hb : d265803 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199547, d265803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199547, d265803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85544 (p : Pattern) (ha : d199712 p = 1) (hb : d265161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199617 q = 1) (hb : d265156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d265156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85365 q ha hb
    | true =>
      simp only [d199617, d265156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85366 q ha hb
  have h5 (q : Pattern) (ha : d199683 q = 1) (hb : d265157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199683, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199709 q = 1) (hb : d265158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199709, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199710 q = 1) (hb : d265159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199710, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199711 q = 1) (hb : d265160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199711, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199712 q = 1) (hb : d265161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199712, d265161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199712, d265161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85545 (p : Pattern) (ha : d199733 p = 1) (hb : d265171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199617 q = 1) (hb : d265156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d265156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85365 q ha hb
    | true =>
      simp only [d199617, d265156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85366 q ha hb
  have h4 (q : Pattern) (ha : d199683 q = 1) (hb : d265157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199683, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199709 q = 1) (hb : d265158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199709, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199710 q = 1) (hb : d265159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199710, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199711 q = 1) (hb : d265160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199711, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199627 q = 1) (hb : d265166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d265166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85368 q ha hb
    | true =>
      simp only [d199627, d265166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85369 q ha hb
  have h13 (q : Pattern) (ha : d199726 q = 1) (hb : d265167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199726, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199730 q = 1) (hb : d265168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199730, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199731 q = 1) (hb : d265169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199731, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199731, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199732 q = 1) (hb : d265170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199732, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199732, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199733 q = 1) (hb : d265171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199733, d265171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199733, d265171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85546 (p : Pattern) (ha : d199753 p = 1) (hb : d265809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199627 q = 1) (hb : d265166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d265166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85368 q ha hb
    | true =>
      simp only [d199627, d265166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85369 q ha hb
  have h3 (q : Pattern) (ha : d199726 q = 1) (hb : d265167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199726, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199730 q = 1) (hb : d265168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199730, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199751 q = 1) (hb : d265169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199751, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199751, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199752 q = 1) (hb : d265170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199752, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199752, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199753 q = 1) (hb : d265809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199753, d265809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199753, d265809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85547 (p : Pattern) (ha : d199866 p = 1) (hb : d265820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199840 q = 1) (hb : d265815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199840, d265815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85405 q ha hb
    | true =>
      simp only [d199840, d265815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85411 q ha hb
  have h3 (q : Pattern) (ha : d199841 q = 1) (hb : d265816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199841, d265816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199841, d265816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199862 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199863 q = 1) (hb : d265817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199863, d265817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199863, d265817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199864 q = 1) (hb : d265818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199864, d265818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199864, d265818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199865 q = 1) (hb : d265819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199865, d265819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199865, d265819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199866 q = 1) (hb : d265820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199866, d265820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199866, d265820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85548 (p : Pattern) (ha : d199879 p = 1) (hb : d265826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199635 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199734 q = 1) (hb : d265172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199734, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85544 q ha hb
    | true =>
      simp only [d199734, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85545 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199748 q = 1) (hb : d265173 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199748, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199748, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199749 q = 1) (hb : d265807 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199749, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199749, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199750 q = 1) (hb : d265808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199750, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199750, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199754 q = 1) (hb : d265810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199754, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199754, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85546 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199756 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199757 q = 1) (hb : d265811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199757, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199757, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199758 q = 1) (hb : d265812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199758, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199758, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199759 q = 1) (hb : d265813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199759, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199759, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199760 q = 1) (hb : d265814 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199760, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199760, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199867 q = 1) (hb : d265821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199867, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199867, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85547 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199874 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199875 q = 1) (hb : d265822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199875, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199875, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199876 q = 1) (hb : d265823 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199876, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199876, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199877 q = 1) (hb : d265824 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199877, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199877, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199878 q = 1) (hb : d265825 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199878, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199878, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199879 q = 1) (hb : d265826 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199879, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199879, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85549 (p : Pattern) (ha : d199885 p = 1) (hb : d265832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199880 q = 1) (hb : d265827 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199880, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199880, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85548 q ha hb
  have h2 (q : Pattern) (ha : d199881 q = 1) (hb : d265828 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199881, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199881, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199882 q = 1) (hb : d265829 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199882, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199882, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199883 q = 1) (hb : d265830 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199883, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199883, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199884 q = 1) (hb : d265831 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199884, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199884, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199885 q = 1) (hb : d265832 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199885, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199885, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85550 (p : Pattern) (ha : d200035 p = 1) (hb : d265440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199945 q = 1) (hb : d265435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d265435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85423 q ha hb
    | true =>
      simp only [d199945, d265435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85424 q ha hb
  have h5 (q : Pattern) (ha : d200000 q = 1) (hb : d265436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d200000, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200032 q = 1) (hb : d265437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200032, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d200033 q = 1) (hb : d265438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200033, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200034 q = 1) (hb : d265439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200034, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200035 q = 1) (hb : d265440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200035, d265440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200035, d265440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85551 (p : Pattern) (ha : d200056 p = 1) (hb : d265450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199945 q = 1) (hb : d265435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d265435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85423 q ha hb
    | true =>
      simp only [d199945, d265435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85424 q ha hb
  have h4 (q : Pattern) (ha : d200000 q = 1) (hb : d265436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200000, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200032 q = 1) (hb : d265437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200032, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d200033 q = 1) (hb : d265438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200033, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200034 q = 1) (hb : d265439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200034, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d200041 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d200046 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199955 q = 1) (hb : d265445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85426 q ha hb
    | true =>
      simp only [d199955, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85427 q ha hb
  have h13 (q : Pattern) (ha : d200049 q = 1) (hb : d265446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d200049, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200053 q = 1) (hb : d265447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200053, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200054 q = 1) (hb : d265448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200054, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d200054, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200055 q = 1) (hb : d265449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200055, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d200055, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200056 q = 1) (hb : d265450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200056, d265450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200056, d265450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85552 (p : Pattern) (ha : d200076 p = 1) (hb : d265839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199955 q = 1) (hb : d265445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85426 q ha hb
    | true =>
      simp only [d199955, d265445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85427 q ha hb
  have h3 (q : Pattern) (ha : d200049 q = 1) (hb : d265446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200049, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200053 q = 1) (hb : d265447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200053, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200074 q = 1) (hb : d265448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200074, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200074, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200075 q = 1) (hb : d265449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200075, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200075, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200076 q = 1) (hb : d265839 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200076, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200076, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85553 (p : Pattern) (ha : d200182 p = 1) (hb : d265850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d200151 q = 1) (hb : d265845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200151, d265845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85464 q ha hb
    | true =>
      simp only [d200151, d265845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85470 q ha hb
  have h3 (q : Pattern) (ha : d200152 q = 1) (hb : d265846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200152, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200152, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200179 q = 1) (hb : d265847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200179, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200179, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200180 q = 1) (hb : d265848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200180, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200180, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200181 q = 1) (hb : d265849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200181, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200181, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200182 q = 1) (hb : d265850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200182, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200182, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85554 (p : Pattern) (ha : d200195 p = 1) (hb : d265856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200057 q = 1) (hb : d265451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200057, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85550 q ha hb
    | true =>
      simp only [d200057, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85551 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200071 q = 1) (hb : d265452 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200071, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200071, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200072 q = 1) (hb : d265837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200072, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200072, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200073 q = 1) (hb : d265838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200073, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200073, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200077 q = 1) (hb : d265840 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200077, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200077, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85552 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d200079 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d200080 q = 1) (hb : d265841 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200080, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200080, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d200081 q = 1) (hb : d265842 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200081, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200081, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d200082 q = 1) (hb : d265843 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200082, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200082, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d200083 q = 1) (hb : d265844 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200083, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200083, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200183 q = 1) (hb : d265851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200183, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200183, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85553 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200190 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200191 q = 1) (hb : d265852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200191, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200191, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200192 q = 1) (hb : d265853 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200192, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200192, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d200193 q = 1) (hb : d265854 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200193, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200193, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d200194 q = 1) (hb : d265855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200194, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200194, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d200195 q = 1) (hb : d265856 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d200195, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200195, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85555 (p : Pattern) (ha : d200201 p = 1) (hb : d265862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200196 q = 1) (hb : d265857 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d200196, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200196, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85554 q ha hb
  have h2 (q : Pattern) (ha : d200197 q = 1) (hb : d265858 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d200197, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200197, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200198 q = 1) (hb : d265859 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d200198, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200198, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200199 q = 1) (hb : d265860 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d200199, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200199, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200200 q = 1) (hb : d265861 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d200200, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200200, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200201 q = 1) (hb : d265862 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d200201, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200201, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85556 (p : Pattern) (ha : d200207 p = 1) (hb : d265868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d198937 q = 1) (hb : d265749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d198937, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85525 q ha hb
    | true =>
      simp only [d198937, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85531 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199211 q = 1) (hb : d265776 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199211, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199211, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85537 q ha hb
  have h3 (q : Pattern) (ha : d199212 q = 1) (hb : d265777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199212, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d199212, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199548 q = 1) (hb : d265804 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199548, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199548, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85543 q ha hb
  have h5 (q : Pattern) (ha : d199549 q = 1) (hb : d265805 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199549, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199549, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199550 q = 1) (hb : d265806 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199550, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199550, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199886 q = 1) (hb : d265833 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199886, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199886, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85549 q ha hb
  have h8 (q : Pattern) (ha : d199887 q = 1) (hb : d265834 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199887, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199887, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199888 q = 1) (hb : d265835 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199888, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199888, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199889 q = 1) (hb : d265836 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d199889, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199889, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200202 q = 1) (hb : d265863 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d200202, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200202, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85555 q ha hb
  have h12 (q : Pattern) (ha : d200203 q = 1) (hb : d265864 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d200203, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200203, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200204 q = 1) (hb : d265865 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d200204, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200204, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200205 q = 1) (hb : d265866 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d200205, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200205, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200206 q = 1) (hb : d265867 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d200206, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200206, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200207 q = 1) (hb : d265868 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d200207, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200207, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro85557 (p : Pattern) (ha : d200213 p = 1) (hb : d265874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200208 q = 1) (hb : d265869 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d200208, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85556 q ha hb
    | true =>
      simp only [d200208, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200209 q = 1) (hb : d265870 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d200209, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200209, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200210 q = 1) (hb : d265871 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d200210, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200210, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200211 q = 1) (hb : d265872 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d200211, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200211, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200212 q = 1) (hb : d265873 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d200212, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200212, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200213 q = 1) (hb : d265874 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d200213, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200213, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85558 (p : Pattern) (ha : d200219 p = 1) (hb : d265880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200214 q = 1) (hb : d265875 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d200214, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85557 q ha hb
    | true =>
      simp only [d200214, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200215 q = 1) (hb : d265876 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d200215, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200215, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200216 q = 1) (hb : d265877 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d200216, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200216, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200217 q = 1) (hb : d265878 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d200217, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200217, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200218 q = 1) (hb : d265879 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d200218, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200218, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200219 q = 1) (hb : d265880 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d200219, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200219, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85559 (p : Pattern) (ha : d200225 p = 1) (hb : d265886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200220 q = 1) (hb : d265881 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d200220, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85558 q ha hb
    | true =>
      simp only [d200220, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200221 q = 1) (hb : d265882 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d200221, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200221, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200222 q = 1) (hb : d265883 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d200222, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200222, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200223 q = 1) (hb : d265884 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d200223, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200223, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200224 q = 1) (hb : d265885 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d200224, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200224, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200225 q = 1) (hb : d265886 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d200225, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200225, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85560 (p : Pattern) (ha : d200231 p = 1) (hb : d265892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200226 q = 1) (hb : d265887 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d200226, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85559 q ha hb
    | true =>
      simp only [d200226, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200227 q = 1) (hb : d265888 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d200227, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200227, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200228 q = 1) (hb : d265889 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d200228, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200228, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200229 q = 1) (hb : d265890 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d200229, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200229, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200230 q = 1) (hb : d265891 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d200230, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200230, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200231 q = 1) (hb : d265892 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d200231, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200231, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85561 (p : Pattern) (ha : d200237 p = 1) (hb : d265898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200232 q = 1) (hb : d265893 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d200232, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85560 q ha hb
    | true =>
      simp only [d200232, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200233 q = 1) (hb : d265894 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d200233, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200233, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200234 q = 1) (hb : d265895 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d200234, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200234, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200235 q = 1) (hb : d265896 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d200235, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200235, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200236 q = 1) (hb : d265897 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d200236, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200236, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200237 q = 1) (hb : d265898 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d200237, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200237, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85562 (p : Pattern) (ha : d200243 p = 1) (hb : d265904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200238 q = 1) (hb : d265899 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d200238, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85561 q ha hb
    | true =>
      simp only [d200238, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200239 q = 1) (hb : d265900 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d200239, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200239, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200240 q = 1) (hb : d265901 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d200240, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200240, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200241 q = 1) (hb : d265902 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d200241, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200241, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200242 q = 1) (hb : d265903 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d200242, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200242, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200243 q = 1) (hb : d265904 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d200243, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200243, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85563 (p : Pattern) (ha : d200249 p = 1) (hb : d265910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d265905 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85562 q ha hb
    | true =>
      simp only [d200244, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d265906 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d265907 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d265908 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d265909 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d265910 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro85564 (p : Pattern) (ha : d202015 p = 1) (hb : d264133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d264069 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202011 q = 1) (hb : d264129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202011, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202012 q = 1) (hb : d264130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202012, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202013 q = 1) (hb : d264131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202013, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202014 q = 1) (hb : d264132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202014, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202015 q = 1) (hb : d264133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d264133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d264133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85565 (p : Pattern) (ha : d202020 p = 1) (hb : d264140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d264069 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202011 q = 1) (hb : d264129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202011, d264129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202012 q = 1) (hb : d264130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202012, d264130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202013 q = 1) (hb : d264131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202013, d264131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202014 q = 1) (hb : d264132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202014, d264132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25282 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d264076 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202016 q = 1) (hb : d264136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202016, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202017 q = 1) (hb : d264137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202017, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202018 q = 1) (hb : d264138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202018, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202019 q = 1) (hb : d264139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202019, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202020 q = 1) (hb : d264140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d264140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202020, d264140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85566 (p : Pattern) (ha : d202027 p = 1) (hb : d265700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d264076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202016 q = 1) (hb : d264136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202016, d264136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d264137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202017, d264137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d264138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d264138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d264139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d264139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d265700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d265700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d265700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85567 (p : Pattern) (ha : d202037 p = 1) (hb : d265710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d264112 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202033 q = 1) (hb : d265706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d265706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202033, d265706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d265707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d265707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202034, d265707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d265708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d265708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d265708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d265709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d265709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d265709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d265710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d265710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d265710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85568 (p : Pattern) (ha : d202043 p = 1) (hb : d265716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202021 q = 1) (hb : d264141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d264141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85564 q ha hb
    | true =>
      simp only [d202021, d264141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85565 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202022 q = 1) (hb : d264142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d264142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202022, d264142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202023 q = 1) (hb : d265698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d265698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202023, d265698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202024 q = 1) (hb : d265699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d265699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202024, d265699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202028 q = 1) (hb : d265701 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d265701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202028, d265701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85566 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202029 q = 1) (hb : d265702 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d265702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202029, d265702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202030 q = 1) (hb : d265703 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d265703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202030, d265703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202031 q = 1) (hb : d265704 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d265704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202031, d265704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202032 q = 1) (hb : d265705 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d265705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202032, d265705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202038 q = 1) (hb : d265711 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d265711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202038, d265711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85567 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202039 q = 1) (hb : d265712 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d265712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202039, d265712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202040 q = 1) (hb : d265713 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d265713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202040, d265713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202041 q = 1) (hb : d265714 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d265714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202041, d265714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202042 q = 1) (hb : d265715 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d265715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202042, d265715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202043 q = 1) (hb : d265716 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d265716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202043, d265716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85569 (p : Pattern) (ha : d202049 p = 1) (hb : d265722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d202006 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47842 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d202007 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d202008 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d202009 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d202010 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202044 q = 1) (hb : d265717 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d265717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202044, d265717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85568 q ha hb
  have h8 (q : Pattern) (ha : d202045 q = 1) (hb : d265718 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d265718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202045, d265718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202046 q = 1) (hb : d265719 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d265719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202046, d265719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202047 q = 1) (hb : d265720 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d265720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202047, d265720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202048 q = 1) (hb : d265721 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d265721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202048, d265721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202049 q = 1) (hb : d265722 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d265722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d202049, d265722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro85570 (p : Pattern) (ha : d202054 p = 1) (hb : d264303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d264298 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202050 q = 1) (hb : d264299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202050, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202051 q = 1) (hb : d264300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202051, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202052 q = 1) (hb : d264301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202052, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202053 q = 1) (hb : d264302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202053, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202054 q = 1) (hb : d264303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d264303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d264303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85571 (p : Pattern) (ha : d202059 p = 1) (hb : d264313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d264298 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202050 q = 1) (hb : d264299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202050, d264299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202051 q = 1) (hb : d264300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202051, d264300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202052 q = 1) (hb : d264301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202052, d264301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202053 q = 1) (hb : d264302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202053, d264302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25531 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25536 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d264308 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202055 q = 1) (hb : d264309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202055, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202056 q = 1) (hb : d264310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202056, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202057 q = 1) (hb : d264311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202057, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202058 q = 1) (hb : d264312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202058, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202059 q = 1) (hb : d264313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d264313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202059, d264313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85572 (p : Pattern) (ha : d202066 p = 1) (hb : d265725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d264308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202055 q = 1) (hb : d264309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202055, d264309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d264310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202056, d264310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d264311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d264311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d264312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d264312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d265725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d265725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d265725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85573 (p : Pattern) (ha : d202076 p = 1) (hb : d265736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202072 q = 1) (hb : d265732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d265732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202072, d265732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202073 q = 1) (hb : d265733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d265733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202073, d265733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202074 q = 1) (hb : d265734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d265734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202074, d265734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202075 q = 1) (hb : d265735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d265735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202075, d265735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202076 q = 1) (hb : d265736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d265736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202076, d265736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85574 (p : Pattern) (ha : d202082 p = 1) (hb : d265742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202060 q = 1) (hb : d264314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d264314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85570 q ha hb
    | true =>
      simp only [d202060, d264314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85571 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202061 q = 1) (hb : d264315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d264315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202061, d264315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202062 q = 1) (hb : d265723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d265723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202062, d265723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202063 q = 1) (hb : d265724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d265724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202063, d265724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202067 q = 1) (hb : d265726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d265726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202067, d265726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85572 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25572 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202068 q = 1) (hb : d265727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d265727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202068, d265727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202069 q = 1) (hb : d265728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d265728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202069, d265728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202070 q = 1) (hb : d265729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d265729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202070, d265729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202071 q = 1) (hb : d265730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d265730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202071, d265730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202077 q = 1) (hb : d265737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d265737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202077, d265737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85573 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202078 q = 1) (hb : d265738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d265738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202078, d265738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202079 q = 1) (hb : d265739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d265739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202079, d265739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202080 q = 1) (hb : d265740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d265740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202080, d265740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202081 q = 1) (hb : d265741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d265741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202081, d265741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202082 q = 1) (hb : d265742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d265742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202082, d265742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85575 (p : Pattern) (ha : d202088 p = 1) (hb : d265748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202083 q = 1) (hb : d265743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d265743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202083, d265743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85574 q ha hb
  have h2 (q : Pattern) (ha : d202084 q = 1) (hb : d265744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d265744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202084, d265744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202085 q = 1) (hb : d265745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d265745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202085, d265745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202086 q = 1) (hb : d265746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d265746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202086, d265746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202087 q = 1) (hb : d265747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d265747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202087, d265747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202088 q = 1) (hb : d265748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d265748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202088, d265748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85576 (p : Pattern) (ha : d202094 p = 1) (hb : d264556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d264551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202090 q = 1) (hb : d264552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202090, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202091 q = 1) (hb : d264553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202091, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202092 q = 1) (hb : d264554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202092, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202093 q = 1) (hb : d264555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202093, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202094 q = 1) (hb : d264556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d264556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202094, d264556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85577 (p : Pattern) (ha : d202099 p = 1) (hb : d264566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d264551 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202090 q = 1) (hb : d264552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202090, d264552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202091 q = 1) (hb : d264553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202091, d264553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202092 q = 1) (hb : d264554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202092, d264554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202093 q = 1) (hb : d264555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202093, d264555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25892 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d264561 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202095 q = 1) (hb : d264562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202095, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202096 q = 1) (hb : d264563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202096, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202097 q = 1) (hb : d264564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202097, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202098 q = 1) (hb : d264565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202098, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202099 q = 1) (hb : d264566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d264566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202099, d264566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85578 (p : Pattern) (ha : d202106 p = 1) (hb : d265752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d264561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202095 q = 1) (hb : d264562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202095, d264562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202096 q = 1) (hb : d264563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202096, d264563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202104 q = 1) (hb : d264564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202104, d264564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202105 q = 1) (hb : d264565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202105, d264565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202106 q = 1) (hb : d265752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d265752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202106, d265752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85579 (p : Pattern) (ha : d202116 p = 1) (hb : d265763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202112 q = 1) (hb : d265759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202112, d265759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202112, d265759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202113 q = 1) (hb : d265760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202113, d265760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202113, d265760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202114 q = 1) (hb : d265761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202114, d265761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202114, d265761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202115 q = 1) (hb : d265762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202115, d265762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202115, d265762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202116 q = 1) (hb : d265763 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202116, d265763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202116, d265763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85580 (p : Pattern) (ha : d202122 p = 1) (hb : d265769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25743 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202100 q = 1) (hb : d264567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202100, d264567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85576 q ha hb
    | true =>
      simp only [d202100, d264567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85577 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202101 q = 1) (hb : d264568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202101, d264568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202101, d264568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202102 q = 1) (hb : d265750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202102, d265750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202102, d265750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202103 q = 1) (hb : d265751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202103, d265751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202103, d265751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202107 q = 1) (hb : d265753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202107, d265753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202107, d265753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85578 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25928 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202108 q = 1) (hb : d265754 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202108, d265754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202108, d265754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202109 q = 1) (hb : d265755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202109, d265755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202109, d265755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202110 q = 1) (hb : d265756 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202110, d265756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202110, d265756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202111 q = 1) (hb : d265757 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202111, d265757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202111, d265757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202117 q = 1) (hb : d265764 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202117, d265764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202117, d265764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85579 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26065 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202118 q = 1) (hb : d265765 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202118, d265765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202118, d265765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202119 q = 1) (hb : d265766 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202119, d265766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202119, d265766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202120 q = 1) (hb : d265767 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202120, d265767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202120, d265767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202121 q = 1) (hb : d265768 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202121, d265768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202121, d265768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202122 q = 1) (hb : d265769 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202122, d265769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202122, d265769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85581 (p : Pattern) (ha : d202128 p = 1) (hb : d265775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202123 q = 1) (hb : d265770 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202123, d265770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202123, d265770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85580 q ha hb
  have h2 (q : Pattern) (ha : d202124 q = 1) (hb : d265771 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202124, d265771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202124, d265771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202125 q = 1) (hb : d265772 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202125, d265772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202125, d265772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202126 q = 1) (hb : d265773 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202126, d265773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202126, d265773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202127 q = 1) (hb : d265774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202127, d265774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202127, d265774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202128 q = 1) (hb : d265775 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202128, d265775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202128, d265775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85582 (p : Pattern) (ha : d202135 p = 1) (hb : d264852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d264847 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202131 q = 1) (hb : d264848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202131, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202132 q = 1) (hb : d264849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202132, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202133 q = 1) (hb : d264850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202133, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202134 q = 1) (hb : d264851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202134, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202135 q = 1) (hb : d264852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202135, d264852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202135, d264852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85583 (p : Pattern) (ha : d202140 p = 1) (hb : d264862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d264847 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202131 q = 1) (hb : d264848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202131, d264848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202132 q = 1) (hb : d264849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202132, d264849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202133 q = 1) (hb : d264850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202133, d264850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202134 q = 1) (hb : d264851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202134, d264851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d264857 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202136 q = 1) (hb : d264858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202136, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202137 q = 1) (hb : d264859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202137, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202138 q = 1) (hb : d264860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202138, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202138, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202139 q = 1) (hb : d264861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202139, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202139, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202140 q = 1) (hb : d264862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202140, d264862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202140, d264862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85584 (p : Pattern) (ha : d202147 p = 1) (hb : d265780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d264857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202136 q = 1) (hb : d264858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202136, d264858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202137 q = 1) (hb : d264859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202137, d264859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202145 q = 1) (hb : d264860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202145, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202145, d264860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202146 q = 1) (hb : d264861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202146, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202146, d264861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202147 q = 1) (hb : d265780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202147, d265780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202147, d265780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85585 (p : Pattern) (ha : d202157 p = 1) (hb : d265791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202153 q = 1) (hb : d265787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202153, d265787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202153, d265787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26519 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202154 q = 1) (hb : d265788 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202154, d265788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202154, d265788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202155 q = 1) (hb : d265789 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202155, d265789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202155, d265789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202156 q = 1) (hb : d265790 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202156, d265790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202156, d265790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202157 q = 1) (hb : d265791 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202157, d265791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202157, d265791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85586 (p : Pattern) (ha : d202163 p = 1) (hb : d265797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202141 q = 1) (hb : d264863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202141, d264863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85582 q ha hb
    | true =>
      simp only [d202141, d264863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85583 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202142 q = 1) (hb : d264864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202142, d264864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202142, d264864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202143 q = 1) (hb : d265778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202143, d265778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202143, d265778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202144 q = 1) (hb : d265779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202144, d265779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202144, d265779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202148 q = 1) (hb : d265781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202148, d265781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202148, d265781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85584 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26368 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202149 q = 1) (hb : d265782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202149, d265782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202149, d265782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202150 q = 1) (hb : d265783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202150, d265783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202150, d265783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202151 q = 1) (hb : d265784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202151, d265784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202151, d265784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202152 q = 1) (hb : d265785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202152, d265785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202152, d265785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202158 q = 1) (hb : d265792 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202158, d265792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202158, d265792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85585 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26535 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202159 q = 1) (hb : d265793 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202159, d265793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202159, d265793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202160 q = 1) (hb : d265794 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202160, d265794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202160, d265794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202161 q = 1) (hb : d265795 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202161, d265795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202161, d265795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202162 q = 1) (hb : d265796 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202162, d265796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202162, d265796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202163 q = 1) (hb : d265797 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202163, d265797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202163, d265797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85587 (p : Pattern) (ha : d202169 p = 1) (hb : d265803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202164 q = 1) (hb : d265798 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202164, d265798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202164, d265798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85586 q ha hb
  have h2 (q : Pattern) (ha : d202165 q = 1) (hb : d265799 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202165, d265799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202165, d265799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202166 q = 1) (hb : d265800 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202166, d265800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202166, d265800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202167 q = 1) (hb : d265801 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202167, d265801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202167, d265801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202168 q = 1) (hb : d265802 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202168, d265802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202168, d265802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202169 q = 1) (hb : d265803 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202169, d265803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202169, d265803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85588 (p : Pattern) (ha : d202177 p = 1) (hb : d265161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d265156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202173 q = 1) (hb : d265157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202173, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202174 q = 1) (hb : d265158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202174, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202175 q = 1) (hb : d265159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202175, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202176 q = 1) (hb : d265160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202176, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202177 q = 1) (hb : d265161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202177, d265161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202177, d265161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85589 (p : Pattern) (ha : d202182 p = 1) (hb : d265171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d265156 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202173 q = 1) (hb : d265157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202173, d265157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202174 q = 1) (hb : d265158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202174, d265158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202175 q = 1) (hb : d265159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202175, d265159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202176 q = 1) (hb : d265160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202176, d265160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26793 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d265166 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202178 q = 1) (hb : d265167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202178, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202179 q = 1) (hb : d265168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202179, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202180 q = 1) (hb : d265169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202180, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202180, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202181 q = 1) (hb : d265170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202181, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202181, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202182 q = 1) (hb : d265171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202182, d265171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202182, d265171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85590 (p : Pattern) (ha : d202189 p = 1) (hb : d265809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202178 q = 1) (hb : d265167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202178, d265167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202179 q = 1) (hb : d265168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202179, d265168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202187 q = 1) (hb : d265169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202187, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202187, d265169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202188 q = 1) (hb : d265170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202188, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202188, d265170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202189 q = 1) (hb : d265809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202189, d265809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202189, d265809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85591 (p : Pattern) (ha : d202199 p = 1) (hb : d265820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265815 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202195 q = 1) (hb : d265816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202195, d265816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202195, d265816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202196 q = 1) (hb : d265817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202196, d265817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202196, d265817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202197 q = 1) (hb : d265818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202197, d265818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202197, d265818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202198 q = 1) (hb : d265819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202198, d265819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202198, d265819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202199 q = 1) (hb : d265820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202199, d265820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202199, d265820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85592 (p : Pattern) (ha : d202205 p = 1) (hb : d265826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26634 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202183 q = 1) (hb : d265172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202183, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85588 q ha hb
    | true =>
      simp only [d202183, d265172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85589 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202184 q = 1) (hb : d265173 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202184, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202184, d265173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202185 q = 1) (hb : d265807 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202185, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202185, d265807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202186 q = 1) (hb : d265808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202186, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202186, d265808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202190 q = 1) (hb : d265810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202190, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202190, d265810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85590 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26829 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202191 q = 1) (hb : d265811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202191, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202191, d265811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202192 q = 1) (hb : d265812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202192, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202192, d265812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202193 q = 1) (hb : d265813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202193, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202193, d265813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202194 q = 1) (hb : d265814 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202194, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202194, d265814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202200 q = 1) (hb : d265821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202200, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202200, d265821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85591 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26998 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202201 q = 1) (hb : d265822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202201, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202201, d265822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202202 q = 1) (hb : d265823 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202202, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202202, d265823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202203 q = 1) (hb : d265824 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202203, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202203, d265824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202204 q = 1) (hb : d265825 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202204, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202204, d265825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202205 q = 1) (hb : d265826 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202205, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202205, d265826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85593 (p : Pattern) (ha : d202211 p = 1) (hb : d265832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202206 q = 1) (hb : d265827 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202206, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202206, d265827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85592 q ha hb
  have h2 (q : Pattern) (ha : d202207 q = 1) (hb : d265828 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202207, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202207, d265828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202208 q = 1) (hb : d265829 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202208, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202208, d265829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202209 q = 1) (hb : d265830 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202209, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202209, d265830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202210 q = 1) (hb : d265831 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202210, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202210, d265831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202211 q = 1) (hb : d265832 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202211, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202211, d265832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85594 (p : Pattern) (ha : d202220 p = 1) (hb : d265440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d265435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202216 q = 1) (hb : d265436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202216, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202217 q = 1) (hb : d265437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202217, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202218 q = 1) (hb : d265438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202218, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202219 q = 1) (hb : d265439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202219, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202220 q = 1) (hb : d265440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202220, d265440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202220, d265440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85595 (p : Pattern) (ha : d202225 p = 1) (hb : d265450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d265435 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202216 q = 1) (hb : d265436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202216, d265436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202217 q = 1) (hb : d265437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202217, d265437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202218 q = 1) (hb : d265438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202218, d265438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202219 q = 1) (hb : d265439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202219, d265439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d265445 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202221 q = 1) (hb : d265446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202221, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202222 q = 1) (hb : d265447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202222, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202223 q = 1) (hb : d265448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202223, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202223, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202224 q = 1) (hb : d265449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202224, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202224, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202225 q = 1) (hb : d265450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202225, d265450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202225, d265450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85596 (p : Pattern) (ha : d202232 p = 1) (hb : d265839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265445 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202221 q = 1) (hb : d265446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202221, d265446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202222 q = 1) (hb : d265447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202222, d265447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202230 q = 1) (hb : d265448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202230, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202230, d265448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202231 q = 1) (hb : d265449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202231, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202231, d265449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202232 q = 1) (hb : d265839 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202232, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202232, d265839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85597 (p : Pattern) (ha : d202242 p = 1) (hb : d265850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d265845 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202238 q = 1) (hb : d265846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202238, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202238, d265846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27405 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202239 q = 1) (hb : d265847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202239, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202239, d265847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202240 q = 1) (hb : d265848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202240, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202240, d265848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202241 q = 1) (hb : d265849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202241, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202241, d265849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202242 q = 1) (hb : d265850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202242, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202242, d265850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85598 (p : Pattern) (ha : d202248 p = 1) (hb : d265856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202226 q = 1) (hb : d265451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202226, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85594 q ha hb
    | true =>
      simp only [d202226, d265451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85595 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202227 q = 1) (hb : d265452 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202227, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202227, d265452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202228 q = 1) (hb : d265837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202228, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202228, d265837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202229 q = 1) (hb : d265838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202229, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202229, d265838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202233 q = 1) (hb : d265840 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202233, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202233, d265840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85596 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d27262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202234 q = 1) (hb : d265841 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202234, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202234, d265841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202235 q = 1) (hb : d265842 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202235, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202235, d265842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202236 q = 1) (hb : d265843 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202236, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202236, d265843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202237 q = 1) (hb : d265844 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202237, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202237, d265844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202243 q = 1) (hb : d265851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202243, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202243, d265851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85597 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27421 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202244 q = 1) (hb : d265852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202244, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202244, d265852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202245 q = 1) (hb : d265853 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202245, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202245, d265853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202246 q = 1) (hb : d265854 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202246, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202246, d265854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202247 q = 1) (hb : d265855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202247, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202247, d265855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202248 q = 1) (hb : d265856 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202248, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202248, d265856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85599 (p : Pattern) (ha : d202254 p = 1) (hb : d265862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202249 q = 1) (hb : d265857 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202249, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202249, d265857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85598 q ha hb
  have h2 (q : Pattern) (ha : d202250 q = 1) (hb : d265858 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202250, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202250, d265858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202251 q = 1) (hb : d265859 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202251, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202251, d265859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202252 q = 1) (hb : d265860 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202252, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202252, d265860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202253 q = 1) (hb : d265861 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202253, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202253, d265861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202254 q = 1) (hb : d265862 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202254, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202254, d265862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85600 (p : Pattern) (ha : d202260 p = 1) (hb : d265868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d202089 q = 1) (hb : d265749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202089, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85569 q ha hb
    | true =>
      simp only [d202089, d265749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85575 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202129 q = 1) (hb : d265776 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202129, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202129, d265776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85581 q ha hb
  have h3 (q : Pattern) (ha : d202130 q = 1) (hb : d265777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202130, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202130, d265777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202170 q = 1) (hb : d265804 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202170, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202170, d265804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85587 q ha hb
  have h5 (q : Pattern) (ha : d202171 q = 1) (hb : d265805 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202171, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202171, d265805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202172 q = 1) (hb : d265806 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202172, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202172, d265806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202212 q = 1) (hb : d265833 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202212, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202212, d265833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85593 q ha hb
  have h8 (q : Pattern) (ha : d202213 q = 1) (hb : d265834 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202213, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202213, d265834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202214 q = 1) (hb : d265835 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202214, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202214, d265835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202215 q = 1) (hb : d265836 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202215, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202215, d265836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202255 q = 1) (hb : d265863 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202255, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202255, d265863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85599 q ha hb
  have h12 (q : Pattern) (ha : d202256 q = 1) (hb : d265864 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202256, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202256, d265864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202257 q = 1) (hb : d265865 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202257, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202257, d265865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202258 q = 1) (hb : d265866 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202258, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202258, d265866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202259 q = 1) (hb : d265867 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d202259, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202259, d265867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202260 q = 1) (hb : d265868 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d202260, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202260, d265868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro85601 (p : Pattern) (ha : d202266 p = 1) (hb : d265874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202261 q = 1) (hb : d265869 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d202261, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85600 q ha hb
    | true =>
      simp only [d202261, d265869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202262 q = 1) (hb : d265870 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d202262, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202262, d265870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202263 q = 1) (hb : d265871 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d202263, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202263, d265871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202264 q = 1) (hb : d265872 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d202264, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202264, d265872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202265 q = 1) (hb : d265873 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d202265, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202265, d265873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202266 q = 1) (hb : d265874 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d202266, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202266, d265874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85602 (p : Pattern) (ha : d202272 p = 1) (hb : d265880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202267 q = 1) (hb : d265875 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d202267, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85601 q ha hb
    | true =>
      simp only [d202267, d265875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202268 q = 1) (hb : d265876 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d202268, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202268, d265876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202269 q = 1) (hb : d265877 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d202269, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202269, d265877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202270 q = 1) (hb : d265878 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d202270, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202270, d265878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202271 q = 1) (hb : d265879 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d202271, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202271, d265879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202272 q = 1) (hb : d265880 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d202272, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202272, d265880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85603 (p : Pattern) (ha : d202278 p = 1) (hb : d265886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202273 q = 1) (hb : d265881 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d202273, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85602 q ha hb
    | true =>
      simp only [d202273, d265881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202274 q = 1) (hb : d265882 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d202274, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202274, d265882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202275 q = 1) (hb : d265883 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d202275, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202275, d265883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202276 q = 1) (hb : d265884 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d202276, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202276, d265884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202277 q = 1) (hb : d265885 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d202277, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202277, d265885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202278 q = 1) (hb : d265886 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d202278, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202278, d265886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85604 (p : Pattern) (ha : d202284 p = 1) (hb : d265892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202279 q = 1) (hb : d265887 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d202279, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85603 q ha hb
    | true =>
      simp only [d202279, d265887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202280 q = 1) (hb : d265888 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d202280, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202280, d265888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202281 q = 1) (hb : d265889 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d202281, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202281, d265889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202282 q = 1) (hb : d265890 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d202282, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202282, d265890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202283 q = 1) (hb : d265891 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d202283, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202283, d265891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202284 q = 1) (hb : d265892 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d202284, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202284, d265892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85605 (p : Pattern) (ha : d202290 p = 1) (hb : d265898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202285 q = 1) (hb : d265893 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d202285, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85604 q ha hb
    | true =>
      simp only [d202285, d265893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202286 q = 1) (hb : d265894 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d202286, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202286, d265894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202287 q = 1) (hb : d265895 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d202287, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202287, d265895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202288 q = 1) (hb : d265896 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d202288, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202288, d265896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202289 q = 1) (hb : d265897 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d202289, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202289, d265897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202290 q = 1) (hb : d265898 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d202290, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202290, d265898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85606 (p : Pattern) (ha : d202296 p = 1) (hb : d265904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202291 q = 1) (hb : d265899 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d202291, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85605 q ha hb
    | true =>
      simp only [d202291, d265899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202292 q = 1) (hb : d265900 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d202292, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202292, d265900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202293 q = 1) (hb : d265901 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d202293, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202293, d265901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202294 q = 1) (hb : d265902 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d202294, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202294, d265902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202295 q = 1) (hb : d265903 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d202295, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202295, d265903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202296 q = 1) (hb : d265904 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d202296, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202296, d265904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85607 (p : Pattern) (ha : d202302 p = 1) (hb : d265910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202297 q = 1) (hb : d265905 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d202297, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85606 q ha hb
    | true =>
      simp only [d202297, d265905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202298 q = 1) (hb : d265906 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d202298, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202298, d265906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202299 q = 1) (hb : d265907 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d202299, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202299, d265907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202300 q = 1) (hb : d265908 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d202300, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202300, d265908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202301 q = 1) (hb : d265909 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d202301, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202301, d265909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202302 q = 1) (hb : d265910 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d202302, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202302, d265910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85608 (p : Pattern) (ha : d33214 p = 1) (hb : d318725 p = 1) : d320514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d128 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d129 q = 1) : d44881 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d130 q = 1) (hb : d318724 q = 1) : d44882 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d318724, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130, d318724, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33213 q = 1) (hb : d318725 q = 1) : d179344 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33213, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17 q = 1) (hb : d318725 q = 1) : d17 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33214 q = 1) (hb : d318725 q = 1) : d320514 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33214, d320514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33214, d320514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85609 (p : Pattern) (ha : d33220 p = 1) (hb : d318725 p = 1) : d320520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d318725 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33218 q = 1) (hb : d318725 q = 1) : d320518 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33219 q = 1) (hb : d318725 q = 1) : d320519 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d318725 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33220 q = 1) (hb : d318725 q = 1) : d320520 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33220, d320520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33220, d320520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro85610 (p : Pattern) (ha : d33226 p = 1) (hb : d318725 p = 1) : d320526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33221 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
    | true =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33222 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33223 q = 1) (hb : d318725 q = 1) : d320523 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33224 q = 1) (hb : d318725 q = 1) : d320524 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33224, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33225 q = 1) (hb : d318725 q = 1) : d320525 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33225, d320525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33225, d320525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d318725 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33226 q = 1) (hb : d318725 q = 1) : d320526 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33226, d320526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33226, d320526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85611 (p : Pattern) (ha : d33232 p = 1) (hb : d318725 p = 1) : d320532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
    | true =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d318725 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33230 q = 1) (hb : d318725 q = 1) : d320530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33230, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d318725 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33231 q = 1) (hb : d318725 q = 1) : d320531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33231, d320531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33231, d320531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33232 q = 1) (hb : d318725 q = 1) : d320532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33232, d320532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33232, d320532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro85612 (p : Pattern) (ha : d33238 p = 1) (hb : d318725 p = 1) : d320538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d318725 q = 1) : d320537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33238 q = 1) (hb : d318725 q = 1) : d320538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33238, d320538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33238, d320538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro85613 (p : Pattern) (ha : d265915 p = 1) (hb : d318725 p = 1) : d320544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d318725 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d318725 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33239 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
    | true =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d318725 q = 1) : d320540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265911, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d318725 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d318725 q = 1) : d320541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d318725 q = 1) : d320542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265913, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d318725 q = 1) : d320543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265914, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265915 q = 1) (hb : d318725 q = 1) : d320544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265915, d320544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265915, d320544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85614 (p : Pattern) (ha : d33245 p = 1) (hb : d318725 p = 1) : d320545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d318725 q = 1) : d320537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33245 q = 1) (hb : d318725 q = 1) : d320545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33245, d320545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33245, d320545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85615 (p : Pattern) (ha : d265920 p = 1) (hb : d318725 p = 1) : d320551 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d318725 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d318725 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33239 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
    | true =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d318725 q = 1) : d320540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265911, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d318725 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d318725 q = 1) : d320541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d318725 q = 1) : d320542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265913, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d318725 q = 1) : d320543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265914, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d318725 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d318725 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d33246 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
    | true =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265916 q = 1) (hb : d318725 q = 1) : d320547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265916, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d318725 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d265917 q = 1) (hb : d318725 q = 1) : d320548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265917, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265918 q = 1) (hb : d318725 q = 1) : d320549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265918, d320549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265918, d320549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265919 q = 1) (hb : d318725 q = 1) : d320550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265919, d320550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265919, d320550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d265920 q = 1) (hb : d318725 q = 1) : d320551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265920, d320551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265920, d320551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85616 (p : Pattern) (ha : d265927 p = 1) (hb : d318725 p = 1) : d320558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
    | true =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265916 q = 1) (hb : d318725 q = 1) : d320547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265916, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d318725 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265917 q = 1) (hb : d318725 q = 1) : d320548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265917, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265925 q = 1) (hb : d318725 q = 1) : d320556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265925, d320556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265925, d320556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265926 q = 1) (hb : d318725 q = 1) : d320557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265926, d320557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265926, d320557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265927 q = 1) (hb : d318725 q = 1) : d320558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265927, d320558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265927, d320558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85617 (p : Pattern) (ha : d33269 p = 1) (hb : d318725 p = 1) : d320569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33264 q = 1) (hb : d318725 q = 1) : d320564 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
  have h2 (q : Pattern) (ha : d33221 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
    | true =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33265 q = 1) (hb : d318725 q = 1) : d320565 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33265, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33222 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33266 q = 1) (hb : d318725 q = 1) : d320566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33266, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33267 q = 1) (hb : d318725 q = 1) : d320567 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33267, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33268 q = 1) (hb : d318725 q = 1) : d320568 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33268, d320568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33268, d320568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d318725 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33269 q = 1) (hb : d318725 q = 1) : d320569 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33269, d320569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33269, d320569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85618 (p : Pattern) (ha : d33275 p = 1) (hb : d318725 p = 1) : d320575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33270 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
    | true =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33271 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33272 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d318725 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33273 q = 1) (hb : d318725 q = 1) : d320573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33273, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d318725 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33274 q = 1) (hb : d318725 q = 1) : d320574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33274, d320574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33274, d320574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33275 q = 1) (hb : d318725 q = 1) : d320575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33275, d320575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33275, d320575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro85619 (p : Pattern) (ha : d33281 p = 1) (hb : d318725 p = 1) : d320581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85618 q ha hb
    | true =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d318725 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33278 q = 1) (hb : d318725 q = 1) : d320578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33278, d320578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33278, d320578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33279 q = 1) (hb : d318725 q = 1) : d320579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33279, d320579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33279, d320579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33280 q = 1) (hb : d318725 q = 1) : d320580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33280, d320580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33280, d320580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33281 q = 1) (hb : d318725 q = 1) : d320581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33281, d320581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33281, d320581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85620 (p : Pattern) (ha : d265937 p = 1) (hb : d318725 p = 1) : d320587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d318725 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33282 q = 1) (hb : d318725 q = 1) : d320582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85619 q ha hb
    | true =>
      simp only [d33282, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265933 q = 1) (hb : d318725 q = 1) : d320583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265933, d320583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265933, d320583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d318725 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265934 q = 1) (hb : d318725 q = 1) : d320584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265934, d320584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265934, d320584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265935 q = 1) (hb : d318725 q = 1) : d320585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265935, d320585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265935, d320585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265936 q = 1) (hb : d318725 q = 1) : d320586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265936, d320586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265936, d320586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265937 q = 1) (hb : d318725 q = 1) : d320587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265937, d320587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265937, d320587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85621 (p : Pattern) (ha : d265943 p = 1) (hb : d318725 p = 1) : d320593 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d318725 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265921 q = 1) (hb : d318725 q = 1) : d320552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265921, d320552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85613 q ha hb
    | true =>
      simp only [d265921, d320552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85615 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d318725 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265922 q = 1) (hb : d318725 q = 1) : d320553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265922, d320553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265922, d320553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265923 q = 1) (hb : d318725 q = 1) : d320554 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265923, d320554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265923, d320554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265924 q = 1) (hb : d318725 q = 1) : d320555 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265924, d320555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265924, d320555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265928 q = 1) (hb : d318725 q = 1) : d320559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265928, d320559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265928, d320559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85616 q ha hb
  have h8 (q : Pattern) (ha : d265929 q = 1) (hb : d318725 q = 1) : d320560 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265929, d320560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265929, d320560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d265930 q = 1) (hb : d318725 q = 1) : d320561 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265930, d320561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265930, d320561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d265931 q = 1) (hb : d318725 q = 1) : d320562 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265931, d320562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265931, d320562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265932 q = 1) (hb : d318725 q = 1) : d320563 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265932, d320563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265932, d320563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265938 q = 1) (hb : d318725 q = 1) : d320588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265938, d320588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265938, d320588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85620 q ha hb
  have h13 (q : Pattern) (ha : d265939 q = 1) (hb : d318725 q = 1) : d320589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265939, d320589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265939, d320589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d265940 q = 1) (hb : d318725 q = 1) : d320590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265940, d320590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265940, d320590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d265941 q = 1) (hb : d318725 q = 1) : d320591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265941, d320591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265941, d320591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d265942 q = 1) (hb : d318725 q = 1) : d320592 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265942, d320592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265942, d320592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265943 q = 1) (hb : d318725 q = 1) : d320593 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265943, d320593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265943, d320593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro85622 (p : Pattern) (ha : d33303 p = 1) (hb : d318725 p = 1) : d320603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
    | true =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33303 q = 1) (hb : d318725 q = 1) : d320603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33303, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33303, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro85623 (p : Pattern) (ha : d33310 p = 1) (hb : d318725 p = 1) : d320610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
    | true =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33246 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
    | true =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33306 q = 1) (hb : d318725 q = 1) : d320606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33307 q = 1) (hb : d318725 q = 1) : d320607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33307, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33308 q = 1) (hb : d318725 q = 1) : d320608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33309 q = 1) (hb : d318725 q = 1) : d320609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33310 q = 1) (hb : d318725 q = 1) : d320610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33310, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33310, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro85624 (p : Pattern) (ha : d33421 p = 1) (hb : d318725 p = 1) : d320691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
    | true =>
      simp only [d33239, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d318725 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33421 q = 1) (hb : d318725 q = 1) : d320691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33421, d320691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33421, d320691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85625 (p : Pattern) (ha : d33315 p = 1) (hb : d318725 p = 1) : d320615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d318725 q = 1) : d320614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33315 q = 1) (hb : d318725 q = 1) : d320615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33315, d320615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33315, d320615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro85626 (p : Pattern) (ha : d33322 p = 1) (hb : d318725 p = 1) : d320622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d318725 q = 1) : d320620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d318725 q = 1) : d320621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33322 q = 1) (hb : d318725 q = 1) : d320622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33322, d320622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33322, d320622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro85627 (p : Pattern) (ha : d33327 p = 1) (hb : d318725 p = 1) : d320626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d128 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d129 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310 q = 1) (hb : d318724 q = 1) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33326 q = 1) (hb : d318725 q = 1) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13 q = 1) (hb : d128 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d13 q = 1) (hb : d129 q = 1) : d44881 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h17 (q : Pattern) (ha : d130 q = 1) (hb : d318724 q = 1) : d44882 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d318724, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d130, d318724, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d33213 q = 1) (hb : d318725 q = 1) : d179344 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d33213, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h19 (q : Pattern) (ha : d33327 q = 1) (hb : d318725 q = 1) : d320626 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33327, d320626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33327, d320626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85628 (p : Pattern) (ha : d33333 p = 1) (hb : d318725 p = 1) : d320632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33331 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33332 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d318725 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33218 q = 1) (hb : d318725 q = 1) : d320518 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33219 q = 1) (hb : d318725 q = 1) : d320519 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33333 q = 1) (hb : d318725 q = 1) : d320632 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33333, d320632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33333, d320632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro85629 (p : Pattern) (ha : d33341 p = 1) (hb : d318725 p = 1) : d320640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33339 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33340 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d318725 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33341 q = 1) (hb : d318725 q = 1) : d320640 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33341, d320640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33341, d320640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85630 (p : Pattern) (ha : d33347 p = 1) (hb : d318725 p = 1) : d320646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
    | true =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d318725 q = 1) : d320635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d318725 q = 1) : d320636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33221 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
    | true =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33222 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33223 q = 1) (hb : d318725 q = 1) : d320523 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33224 q = 1) (hb : d318725 q = 1) : d320524 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33224, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33338 q = 1) (hb : d318725 q = 1) : d320637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33338, d320637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33338, d320637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33344 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33345 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d33346 q = 1) (hb : d318725 q = 1) : d320645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33346, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33347 q = 1) (hb : d318725 q = 1) : d320646 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33347, d320646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33347, d320646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro85631 (p : Pattern) (ha : d33353 p = 1) (hb : d318725 p = 1) : d320652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85630 q ha hb
    | true =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
    | true =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d318725 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33230 q = 1) (hb : d318725 q = 1) : d320530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33230, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33352 q = 1) (hb : d318725 q = 1) : d320651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33352, d320651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33352, d320651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33353 q = 1) (hb : d318725 q = 1) : d320652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33353, d320652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33353, d320652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro85632 (p : Pattern) (ha : d33359 p = 1) (hb : d318725 p = 1) : d320658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d318725 q = 1) : d320653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85631 q ha hb
    | true =>
      simp only [d33354, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d318725 q = 1) : d320654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d318725 q = 1) : d320655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d318725 q = 1) : d320656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d318725 q = 1) : d320657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33359 q = 1) (hb : d318725 q = 1) : d320658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33359, d320658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33359, d320658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85633 (p : Pattern) (ha : d33392 p = 1) (hb : d318725 p = 1) : d320664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d318725 q = 1) : d320661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d318725 q = 1) : d320662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d318725 q = 1) : d320663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33392 q = 1) (hb : d318725 q = 1) : d320664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33392, d320664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33392, d320664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85634 (p : Pattern) (ha : d265953 p = 1) (hb : d318725 p = 1) : d320670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d318725 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d318725 q = 1) : d320616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85625 q ha hb
    | true =>
      simp only [d33316, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d318725 q = 1) : d320617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d318725 q = 1) : d320618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d318725 q = 1) : d320619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d318725 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d318725 q = 1) : d320623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85626 q ha hb
    | true =>
      simp only [d33323, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d318725 q = 1) : d320624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d318725 q = 1) : d320625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d318725 q = 1) : d320659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85632 q ha hb
    | true =>
      simp only [d33360, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d318725 q = 1) : d320660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d318725 q = 1) : d320665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85633 q ha hb
    | true =>
      simp only [d33393, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d318725 q = 1) : d320666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d318725 q = 1) : d320667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d318725 q = 1) : d320668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d318725 q = 1) : d320669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265953 q = 1) (hb : d318725 q = 1) : d320670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d320670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d320670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro85635 (p : Pattern) (ha : d33399 p = 1) (hb : d318725 p = 1) : d320671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d318725 q = 1) : d320614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33399 q = 1) (hb : d318725 q = 1) : d320671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33399, d320671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33399, d320671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85636 (p : Pattern) (ha : d33404 p = 1) (hb : d318725 p = 1) : d320676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d318725 q = 1) : d320620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d318725 q = 1) : d320621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33404 q = 1) (hb : d318725 q = 1) : d320676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33404, d320676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33404, d320676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85637 (p : Pattern) (ha : d33408 p = 1) (hb : d318725 p = 1) : d320680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d318725 q = 1) : d320653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85631 q ha hb
    | true =>
      simp only [d33354, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d318725 q = 1) : d320654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d318725 q = 1) : d320655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d318725 q = 1) : d320656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d318725 q = 1) : d320657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33408 q = 1) (hb : d318725 q = 1) : d320680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33408, d320680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33408, d320680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85638 (p : Pattern) (ha : d33413 p = 1) (hb : d318725 p = 1) : d320683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85611 q ha hb
    | true =>
      simp only [d33233, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d318725 q = 1) : d320661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d318725 q = 1) : d320662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d318725 q = 1) : d320663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33413 q = 1) (hb : d318725 q = 1) : d320683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33413, d320683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33413, d320683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85639 (p : Pattern) (ha : d265958 p = 1) (hb : d318725 p = 1) : d320689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d318725 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d318725 q = 1) : d320616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85625 q ha hb
    | true =>
      simp only [d33316, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d318725 q = 1) : d320617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d318725 q = 1) : d320618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d318725 q = 1) : d320619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d318725 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d318725 q = 1) : d320623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85626 q ha hb
    | true =>
      simp only [d33323, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d318725 q = 1) : d320624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d318725 q = 1) : d320625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d318725 q = 1) : d320659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85632 q ha hb
    | true =>
      simp only [d33360, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85612 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d318725 q = 1) : d320660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d318725 q = 1) : d320665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85633 q ha hb
    | true =>
      simp only [d33393, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d318725 q = 1) : d320666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d318725 q = 1) : d320667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d318725 q = 1) : d320668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d318725 q = 1) : d320669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d318725 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d33400 q = 1) (hb : d318725 q = 1) : d320672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33400, d320672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85635 q ha hb
    | true =>
      simp only [d33400, d320672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33401 q = 1) (hb : d318725 q = 1) : d320673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33401, d320673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33401, d320673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d33402 q = 1) (hb : d318725 q = 1) : d320674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33402, d320674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33402, d320674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d33403 q = 1) (hb : d318725 q = 1) : d320675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33403, d320675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33403, d320675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d318725 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d33405 q = 1) (hb : d318725 q = 1) : d320677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33405, d320677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85636 q ha hb
    | true =>
      simp only [d33405, d320677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d33406 q = 1) (hb : d318725 q = 1) : d320678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33406, d320678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33406, d320678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33407 q = 1) (hb : d318725 q = 1) : d320679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33407, d320679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33407, d320679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33409 q = 1) (hb : d318725 q = 1) : d320681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85637 q ha hb
    | true =>
      simp only [d33409, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
  have h27 (q : Pattern) (ha : d265954 q = 1) (hb : d318725 q = 1) : d320682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d265954, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d33414 q = 1) (hb : d318725 q = 1) : d320684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85638 q ha hb
    | true =>
      simp only [d33414, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d33415 q = 1) (hb : d318725 q = 1) : d320685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d33415, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d265955 q = 1) (hb : d318725 q = 1) : d320686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d265955, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d265956 q = 1) (hb : d318725 q = 1) : d320687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d320687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d265956, d320687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d265957 q = 1) (hb : d318725 q = 1) : d320688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d320688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265957, d320688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d265958 q = 1) (hb : d318725 q = 1) : d320689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d320689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265958, d320689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro85640 (p : Pattern) (ha : d265965 p = 1) (hb : d318725 p = 1) : d320698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33409 q = 1) (hb : d318725 q = 1) : d320681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85637 q ha hb
    | true =>
      simp only [d33409, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
  have h2 (q : Pattern) (ha : d265954 q = 1) (hb : d318725 q = 1) : d320682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265954, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33414 q = 1) (hb : d318725 q = 1) : d320684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85638 q ha hb
    | true =>
      simp only [d33414, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33415 q = 1) (hb : d318725 q = 1) : d320685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33415, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d318725 q = 1) : d320686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265955, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d318725 q = 1) : d320696 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d320696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d320696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d318725 q = 1) : d320697 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d320697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d320697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d318725 q = 1) : d320698 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d320698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d320698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85641 (p : Pattern) (ha : d33444 p = 1) (hb : d318725 p = 1) : d320714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d318725 q = 1) : d320704 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
    | true =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d318725 q = 1) : d320705 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d318725 q = 1) : d320706 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d318725 q = 1) : d320707 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33264 q = 1) (hb : d318725 q = 1) : d320564 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
  have h8 (q : Pattern) (ha : d33221 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85609 q ha hb
    | true =>
      simp only [d33221, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33265 q = 1) (hb : d318725 q = 1) : d320565 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33265, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33222 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33222, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33266 q = 1) (hb : d318725 q = 1) : d320566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33266, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33267 q = 1) (hb : d318725 q = 1) : d320567 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33267, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33438 q = 1) (hb : d318725 q = 1) : d320708 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33438, d320708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33438, d320708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33439 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
  have h15 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33440 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33441 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33442 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d33443 q = 1) (hb : d318725 q = 1) : d320713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33443, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d33444 q = 1) (hb : d318725 q = 1) : d320714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33444, d320714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33444, d320714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro85642 (p : Pattern) (ha : d33450 p = 1) (hb : d318725 p = 1) : d320720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d318725 q = 1) : d320715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85641 q ha hb
    | true =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d318725 q = 1) : d320716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d318725 q = 1) : d320717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33270 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
    | true =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33271 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33272 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33448 q = 1) (hb : d318725 q = 1) : d320718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d318725 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33273 q = 1) (hb : d318725 q = 1) : d320573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33273, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33449 q = 1) (hb : d318725 q = 1) : d320719 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33449, d320719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33449, d320719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33450 q = 1) (hb : d318725 q = 1) : d320720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33450, d320720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33450, d320720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro85643 (p : Pattern) (ha : d33456 p = 1) (hb : d318725 p = 1) : d320726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33451 q = 1) (hb : d318725 q = 1) : d320721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33451, d320721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85642 q ha hb
    | true =>
      simp only [d33451, d320721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33452 q = 1) (hb : d318725 q = 1) : d320722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33452, d320722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33452, d320722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33276 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85618 q ha hb
    | true =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33277 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33453 q = 1) (hb : d318725 q = 1) : d320723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33453, d320723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33453, d320723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33454 q = 1) (hb : d318725 q = 1) : d320724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33454, d320724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33454, d320724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33455 q = 1) (hb : d318725 q = 1) : d320725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33455, d320725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33455, d320725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33456 q = 1) (hb : d318725 q = 1) : d320726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33456, d320726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33456, d320726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85644 (p : Pattern) (ha : d33481 p = 1) (hb : d318725 p = 1) : d320732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85618 q ha hb
    | true =>
      simp only [d33276, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33478 q = 1) (hb : d318725 q = 1) : d320729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33478, d320729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33478, d320729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33479 q = 1) (hb : d318725 q = 1) : d320730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33479, d320730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33479, d320730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33480 q = 1) (hb : d318725 q = 1) : d320731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33480, d320731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33480, d320731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33481 q = 1) (hb : d318725 q = 1) : d320732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33481, d320732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33481, d320732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85645 (p : Pattern) (ha : d265975 p = 1) (hb : d318725 p = 1) : d320738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33457 q = 1) (hb : d318725 q = 1) : d320727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33457, d320727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85643 q ha hb
    | true =>
      simp only [d33457, d320727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85619 q ha hb
  have h2 (q : Pattern) (ha : d265971 q = 1) (hb : d318725 q = 1) : d320728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d320728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265971, d320728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33482 q = 1) (hb : d318725 q = 1) : d320733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33482, d320733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85644 q ha hb
    | true =>
      simp only [d33482, d320733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33483 q = 1) (hb : d318725 q = 1) : d320734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33483, d320734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33483, d320734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d318725 q = 1) : d320735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d320735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265972, d320735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d318725 q = 1) : d320736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d320736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d320736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d318725 q = 1) : d320737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d320737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d320737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d318725 q = 1) : d320738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d320738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d320738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85646 (p : Pattern) (ha : d265981 p = 1) (hb : d318725 p = 1) : d320744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33304 q = 1) (hb : d318725 q = 1) : d320604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33304, d320604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33304, d320604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85622 q ha hb
  have h2 (q : Pattern) (ha : d33305 q = 1) (hb : d318725 q = 1) : d320605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33305, d320605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33305, d320605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33311 q = 1) (hb : d318725 q = 1) : d320611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85622 q ha hb
    | true =>
      simp only [d33311, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85623 q ha hb
  have h4 (q : Pattern) (ha : d33312 q = 1) (hb : d318725 q = 1) : d320612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33312, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33313 q = 1) (hb : d318725 q = 1) : d320613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33313, d320613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33313, d320613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265959 q = 1) (hb : d318725 q = 1) : d320690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d320690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85634 q ha hb
    | true =>
      simp only [d265959, d320690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85639 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d318725 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33422 q = 1) (hb : d318725 q = 1) : d320692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33422, d320692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85624 q ha hb
    | true =>
      simp only [d33422, d320692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265960 q = 1) (hb : d318725 q = 1) : d320693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d320693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265960, d320693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265961 q = 1) (hb : d318725 q = 1) : d320694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d320694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265961, d320694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d265962 q = 1) (hb : d318725 q = 1) : d320695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d320695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265962, d320695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265966 q = 1) (hb : d318725 q = 1) : d320699 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d320699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265966, d320699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85640 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d318725 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d265967 q = 1) (hb : d318725 q = 1) : d320700 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d320700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265967, d320700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265968 q = 1) (hb : d318725 q = 1) : d320701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d320701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265968, d320701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d265969 q = 1) (hb : d318725 q = 1) : d320702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d320702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265969, d320702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d265970 q = 1) (hb : d318725 q = 1) : d320703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d320703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265970, d320703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265976 q = 1) (hb : d318725 q = 1) : d320739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d320739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265976, d320739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85645 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d318725 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d265977 q = 1) (hb : d318725 q = 1) : d320740 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d320740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265977, d320740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d265978 q = 1) (hb : d318725 q = 1) : d320741 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d320741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d265978, d320741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d265979 q = 1) (hb : d318725 q = 1) : d320742 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d320742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265979, d320742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d265980 q = 1) (hb : d318725 q = 1) : d320743 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d320743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265980, d320743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d265981 q = 1) (hb : d318725 q = 1) : d320744 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d320744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265981, d320744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro85647 (p : Pattern) (ha : d265987 p = 1) (hb : d318725 p = 1) : d320750 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d318725 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d265944 q = 1) (hb : d318725 q = 1) : d320594 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265944, d320594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265944, d320594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85621 q ha hb
  have h3 (q : Pattern) (ha : d265945 q = 1) (hb : d318725 q = 1) : d320595 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265945, d320595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265945, d320595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d265946 q = 1) (hb : d318725 q = 1) : d320596 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265946, d320596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265946, d320596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265947 q = 1) (hb : d318725 q = 1) : d320597 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265947, d320597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265947, d320597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265948 q = 1) (hb : d318725 q = 1) : d320598 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265948, d320598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265948, d320598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d318725 q = 1) : d320745 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d320745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d320745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85646 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d318725 q = 1) : d320746 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d320746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d320746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d318725 q = 1) : d320747 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d320747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d320747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d318725 q = 1) : d320748 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d320748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d320748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d318725 q = 1) : d320749 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d320749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d320749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d318725 q = 1) : d320750 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d320750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265987, d320750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro85648 (p : Pattern) (ha : d33502 p = 1) (hb : d318725 p = 1) : d320753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85630 q ha hb
    | true =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
    | true =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33500 q = 1) (hb : d318725 q = 1) : d320751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33500, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33501 q = 1) (hb : d318725 q = 1) : d320752 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33501, d320752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33501, d320752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33502 q = 1) (hb : d318725 q = 1) : d320753 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33502, d320753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33502, d320753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro85649 (p : Pattern) (ha : d33506 p = 1) (hb : d318725 p = 1) : d320757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
    | true =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33500 q = 1) (hb : d318725 q = 1) : d320751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33500, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33505 q = 1) (hb : d318725 q = 1) : d320756 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33505, d320756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33505, d320756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33506 q = 1) (hb : d318725 q = 1) : d320757 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33506, d320757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33506, d320757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85650 (p : Pattern) (ha : d33512 p = 1) (hb : d318725 p = 1) : d320763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d318725 q = 1) : d320762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33512 q = 1) (hb : d318725 q = 1) : d320763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33512, d320763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33512, d320763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85651 (p : Pattern) (ha : d33516 p = 1) (hb : d318725 p = 1) : d320767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d318725 q = 1) : d320766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33516 q = 1) (hb : d318725 q = 1) : d320767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33516, d320767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33516, d320767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85652 (p : Pattern) (ha : d33522 p = 1) (hb : d318725 p = 1) : d320773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85650 q ha hb
    | true =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85651 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33522 q = 1) (hb : d318725 q = 1) : d320773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33522, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33522, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85653 (p : Pattern) (ha : d33525 p = 1) (hb : d318725 p = 1) : d320776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d318725 q = 1) : d320762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33525 q = 1) (hb : d318725 q = 1) : d320776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33525, d320776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33525, d320776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85654 (p : Pattern) (ha : d33526 p = 1) (hb : d318725 p = 1) : d320777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d318725 q = 1) : d320766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33526 q = 1) (hb : d318725 q = 1) : d320777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33526, d320777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33526, d320777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85655 (p : Pattern) (ha : d33532 p = 1) (hb : d318725 p = 1) : d320783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85650 q ha hb
    | true =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85651 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33527 q = 1) (hb : d318725 q = 1) : d320778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85653 q ha hb
    | true =>
      simp only [d33527, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85654 q ha hb
  have h7 (q : Pattern) (ha : d33528 q = 1) (hb : d318725 q = 1) : d320779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33529 q = 1) (hb : d318725 q = 1) : d320780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33529, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33530 q = 1) (hb : d318725 q = 1) : d320781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33531 q = 1) (hb : d318725 q = 1) : d320782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33532 q = 1) (hb : d318725 q = 1) : d320783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33532, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33532, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85656 (p : Pattern) (ha : d33688 p = 1) (hb : d318725 p = 1) : d320887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85650 q ha hb
    | true =>
      simp only [d33517, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85651 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33683 q = 1) (hb : d318725 q = 1) : d320882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85651 q ha hb
    | true =>
      simp only [d33683, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33684 q = 1) (hb : d318725 q = 1) : d320883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33685 q = 1) (hb : d318725 q = 1) : d320884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33685, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33686 q = 1) (hb : d318725 q = 1) : d320885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33687 q = 1) (hb : d318725 q = 1) : d320886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33688 q = 1) (hb : d318725 q = 1) : d320887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33688, d320887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33688, d320887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85657 (p : Pattern) (ha : d33694 p = 1) (hb : d318725 p = 1) : d320893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33683 q = 1) (hb : d318725 q = 1) : d320882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85651 q ha hb
    | true =>
      simp only [d33683, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33684 q = 1) (hb : d318725 q = 1) : d320883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33685 q = 1) (hb : d318725 q = 1) : d320884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33685, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33686 q = 1) (hb : d318725 q = 1) : d320885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33687 q = 1) (hb : d318725 q = 1) : d320886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33689 q = 1) (hb : d318725 q = 1) : d320888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85654 q ha hb
    | true =>
      simp only [d33689, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33690 q = 1) (hb : d318725 q = 1) : d320889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33691 q = 1) (hb : d318725 q = 1) : d320890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33691, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33692 q = 1) (hb : d318725 q = 1) : d320891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33693 q = 1) (hb : d318725 q = 1) : d320892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33694 q = 1) (hb : d318725 q = 1) : d320893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33694, d320893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33694, d320893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85658 (p : Pattern) (ha : d33703 p = 1) (hb : d318725 p = 1) : d320902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33689 q = 1) (hb : d318725 q = 1) : d320888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85654 q ha hb
    | true =>
      simp only [d33689, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33690 q = 1) (hb : d318725 q = 1) : d320889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33691 q = 1) (hb : d318725 q = 1) : d320890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33691, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33692 q = 1) (hb : d318725 q = 1) : d320891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33693 q = 1) (hb : d318725 q = 1) : d320892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33703 q = 1) (hb : d318725 q = 1) : d320902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33703, d320902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33703, d320902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85659 (p : Pattern) (ha : d33746 p = 1) (hb : d318725 p = 1) : d320945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33270 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
    | true =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33271 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33272 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33736 q = 1) (hb : d318725 q = 1) : d320935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33736, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33736, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33745 q = 1) (hb : d318725 q = 1) : d320944 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33745, d320944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33745, d320944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33746 q = 1) (hb : d318725 q = 1) : d320945 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33746, d320945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33746, d320945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro85660 (p : Pattern) (ha : d33802 p = 1) (hb : d318725 p = 1) : d320968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33747 q = 1) (hb : d318725 q = 1) : d320946 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33747, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85659 q ha hb
    | true =>
      simp only [d33747, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33748 q = 1) (hb : d318725 q = 1) : d320947 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33748, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33748, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33799 q = 1) (hb : d318725 q = 1) : d320965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33799, d320965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33799, d320965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33800 q = 1) (hb : d318725 q = 1) : d320966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33800, d320966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33800, d320966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33801 q = 1) (hb : d318725 q = 1) : d320967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33801, d320967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33801, d320967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33802 q = 1) (hb : d318725 q = 1) : d320968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33802, d320968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33802, d320968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85661 (p : Pattern) (ha : d33808 p = 1) (hb : d318725 p = 1) : d320974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33803 q = 1) (hb : d318725 q = 1) : d320969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33803, d320969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85660 q ha hb
    | true =>
      simp only [d33803, d320969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33804 q = 1) (hb : d318725 q = 1) : d320970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33804, d320970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33804, d320970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33805 q = 1) (hb : d318725 q = 1) : d320971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33805, d320971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33805, d320971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33806 q = 1) (hb : d318725 q = 1) : d320972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33806, d320972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33806, d320972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33807 q = 1) (hb : d318725 q = 1) : d320973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33807, d320973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33807, d320973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33808 q = 1) (hb : d318725 q = 1) : d320974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33808, d320974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33808, d320974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85662 (p : Pattern) (ha : d33537 p = 1) (hb : d318725 p = 1) : d320788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33536 q = 1) (hb : d318725 q = 1) : d320787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33536, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33536, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33537 q = 1) (hb : d318725 q = 1) : d320788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33537, d320788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33537, d320788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85663 (p : Pattern) (ha : d33539 p = 1) (hb : d318725 p = 1) : d320790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33538 q = 1) (hb : d318725 q = 1) : d320789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33538, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33538, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33539 q = 1) (hb : d318725 q = 1) : d320790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33539, d320790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33539, d320790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85664 (p : Pattern) (ha : d33546 p = 1) (hb : d318725 p = 1) : d320797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33544 q = 1) (hb : d318725 q = 1) : d320795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33544, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33544, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33545 q = 1) (hb : d318725 q = 1) : d320796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33545, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33545, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33546 q = 1) (hb : d318725 q = 1) : d320797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33546, d320797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33546, d320797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85665 (p : Pattern) (ha : d33549 p = 1) (hb : d318725 p = 1) : d320800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33547 q = 1) (hb : d318725 q = 1) : d320798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33547, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33547, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33548 q = 1) (hb : d318725 q = 1) : d320799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33548, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33548, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33549 q = 1) (hb : d318725 q = 1) : d320800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33549, d320800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33549, d320800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85666 (p : Pattern) (ha : d33555 p = 1) (hb : d318725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d528 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d33553 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33553, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33553, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1520 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1520, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d33554 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33554, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33554, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h17 (q : Pattern) (ha : d33555 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro85667 (p : Pattern) (ha : d33560 p = 1) (hb : d318725 p = 1) : d320806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d128 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d129 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310 q = 1) (hb : d318724 q = 1) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33326 q = 1) (hb : d318725 q = 1) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13 q = 1) (hb : d128 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d13 q = 1) (hb : d129 q = 1) : d44881 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d534 q = 1) (hb : d318724 q = 1) : d45231 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d318724, d45231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d534, d318724, d45231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d33559 q = 1) (hb : d318725 q = 1) : d320805 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33559, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d33559, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h19 (q : Pattern) (ha : d33560 q = 1) (hb : d318725 q = 1) : d320806 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33560, d320806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33560, d320806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85668 (p : Pattern) (ha : d33566 p = 1) (hb : d318725 p = 1) : d320812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85666 q ha hb
    | true =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33557 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33558 q = 1) (hb : d318725 q = 1) : d320804 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33561 q = 1) (hb : d318725 q = 1) : d320807 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33561, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85667 q ha hb
    | true =>
      simp only [d33561, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33562 q = 1) (hb : d318725 q = 1) : d320808 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33562, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33562, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33563 q = 1) (hb : d318725 q = 1) : d320809 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33563, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33563, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33564 q = 1) (hb : d318725 q = 1) : d320810 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33564, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33564, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33565 q = 1) (hb : d318725 q = 1) : d320811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33565, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33565, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33330 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33331 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33332 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33566 q = 1) (hb : d318725 q = 1) : d320812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33566, d320812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33566, d320812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85669 (p : Pattern) (ha : d33571 p = 1) (hb : d318725 p = 1) : d320817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33331 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33331, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33332 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33332, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33339 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33340 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33571 q = 1) (hb : d318725 q = 1) : d320817 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33571, d320817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33571, d320817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro85670 (p : Pattern) (ha : d33579 p = 1) (hb : d318725 p = 1) : d320825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33577 q = 1) (hb : d318725 q = 1) : d320823 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33577, d320823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33577, d320823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33578 q = 1) (hb : d318725 q = 1) : d320824 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33578, d320824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33578, d320824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33339 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33339, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33340 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33340, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33579 q = 1) (hb : d318725 q = 1) : d320825 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33579, d320825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33579, d320825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro85671 (p : Pattern) (ha : d33585 p = 1) (hb : d318725 p = 1) : d320831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33567 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
    | true =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33568 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33569 q = 1) (hb : d318725 q = 1) : d320815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33569, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33569, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33570 q = 1) (hb : d318725 q = 1) : d320816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33570, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33570, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33572 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
    | true =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33573 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33574 q = 1) (hb : d318725 q = 1) : d320820 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33574, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33574, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33575 q = 1) (hb : d318725 q = 1) : d320821 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33575, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33575, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33576 q = 1) (hb : d318725 q = 1) : d320822 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33576, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33576, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33582 q = 1) (hb : d318725 q = 1) : d320828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33583 q = 1) (hb : d318725 q = 1) : d320829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33344 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33345 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33584 q = 1) (hb : d318725 q = 1) : d320830 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33584, d320830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33584, d320830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33585 q = 1) (hb : d318725 q = 1) : d320831 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33585, d320831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33585, d320831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85672 (p : Pattern) (ha : d33589 p = 1) (hb : d318725 p = 1) : d320835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33344 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33345 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33345, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33346 q = 1) (hb : d318725 q = 1) : d320645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33346, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d318725 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33589 q = 1) (hb : d318725 q = 1) : d320835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33589, d320835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33589, d320835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85673 (p : Pattern) (ha : d33595 p = 1) (hb : d318725 p = 1) : d320841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33586 q = 1) (hb : d318725 q = 1) : d320832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33586, d320832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85671 q ha hb
    | true =>
      simp only [d33586, d320832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85630 q ha hb
  have h2 (q : Pattern) (ha : d33587 q = 1) (hb : d318725 q = 1) : d320833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33587, d320833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33587, d320833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33588 q = 1) (hb : d318725 q = 1) : d320834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33588, d320834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33588, d320834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33590 q = 1) (hb : d318725 q = 1) : d320836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33590, d320836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85630 q ha hb
    | true =>
      simp only [d33590, d320836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85672 q ha hb
  have h5 (q : Pattern) (ha : d33591 q = 1) (hb : d318725 q = 1) : d320837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33591, d320837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33591, d320837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33592 q = 1) (hb : d318725 q = 1) : d320838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33592, d320838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33592, d320838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33593 q = 1) (hb : d318725 q = 1) : d320839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33593, d320839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33593, d320839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33348 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85630 q ha hb
    | true =>
      simp only [d33348, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
  have h9 (q : Pattern) (ha : d33349 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33350 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d33227 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85610 q ha hb
    | true =>
      simp only [d33227, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33228 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33229 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33351 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33351, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33594 q = 1) (hb : d318725 q = 1) : d320840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33594, d320840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33594, d320840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33595 q = 1) (hb : d318725 q = 1) : d320841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33595, d320841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33595, d320841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro85674 (p : Pattern) (ha : d33601 p = 1) (hb : d318725 p = 1) : d320847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33596 q = 1) (hb : d318725 q = 1) : d320842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33596, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85673 q ha hb
    | true =>
      simp only [d33596, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33597 q = 1) (hb : d318725 q = 1) : d320843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33597, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33597, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33598 q = 1) (hb : d318725 q = 1) : d320844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33598, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33598, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33599 q = 1) (hb : d318725 q = 1) : d320845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33599, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33599, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33600 q = 1) (hb : d318725 q = 1) : d320846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33600, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33600, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33601 q = 1) (hb : d318725 q = 1) : d320847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33601, d320847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33601, d320847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85675 (p : Pattern) (ha : d33651 p = 1) (hb : d318725 p = 1) : d320853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33648 q = 1) (hb : d318725 q = 1) : d320850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33648, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33648, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33649 q = 1) (hb : d318725 q = 1) : d320851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33649, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33649, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33650 q = 1) (hb : d318725 q = 1) : d320852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33650, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33650, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33651 q = 1) (hb : d318725 q = 1) : d320853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33651, d320853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33651, d320853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85676 (p : Pattern) (ha : d265992 p = 1) (hb : d318725 p = 1) : d320859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33540 q = 1) (hb : d318725 q = 1) : d320791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33540, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85662 q ha hb
    | true =>
      simp only [d33540, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85663 q ha hb
  have h2 (q : Pattern) (ha : d33541 q = 1) (hb : d318725 q = 1) : d320792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33541, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33541, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33542 q = 1) (hb : d318725 q = 1) : d320793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33542, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33542, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33543 q = 1) (hb : d318725 q = 1) : d320794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33543, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33543, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33550 q = 1) (hb : d318725 q = 1) : d320801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33550, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85664 q ha hb
    | true =>
      simp only [d33550, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85665 q ha hb
  have h6 (q : Pattern) (ha : d33551 q = 1) (hb : d318725 q = 1) : d320802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33551, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33551, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33552 q = 1) (hb : d318725 q = 1) : d320803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33552, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33552, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33602 q = 1) (hb : d318725 q = 1) : d320848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33602, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85674 q ha hb
    | true =>
      simp only [d33602, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85650 q ha hb
  have h9 (q : Pattern) (ha : d265988 q = 1) (hb : d318725 q = 1) : d320849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265988, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33652 q = 1) (hb : d318725 q = 1) : d320854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33652, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85675 q ha hb
    | true =>
      simp only [d33652, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33653 q = 1) (hb : d318725 q = 1) : d320855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33653, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33653, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265989 q = 1) (hb : d318725 q = 1) : d320856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265989, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265990 q = 1) (hb : d318725 q = 1) : d320857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265990, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265991 q = 1) (hb : d318725 q = 1) : d320858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265991, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265992 q = 1) (hb : d318725 q = 1) : d320859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d320859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d320859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85677 (p : Pattern) (ha : d33658 p = 1) (hb : d318725 p = 1) : d320860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33536 q = 1) (hb : d318725 q = 1) : d320787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33536, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33536, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33658 q = 1) (hb : d318725 q = 1) : d320860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33658, d320860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33658, d320860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85678 (p : Pattern) (ha : d33659 p = 1) (hb : d318725 p = 1) : d320861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33538 q = 1) (hb : d318725 q = 1) : d320789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33538, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33538, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33659 q = 1) (hb : d318725 q = 1) : d320861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33659, d320861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33659, d320861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85679 (p : Pattern) (ha : d33664 p = 1) (hb : d318725 p = 1) : d320866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33544 q = 1) (hb : d318725 q = 1) : d320795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33544, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33544, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33545 q = 1) (hb : d318725 q = 1) : d320796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33545, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33545, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33664 q = 1) (hb : d318725 q = 1) : d320866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33664, d320866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33664, d320866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85680 (p : Pattern) (ha : d33665 p = 1) (hb : d318725 p = 1) : d320867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85649 q ha hb
    | true =>
      simp only [d33507, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33547 q = 1) (hb : d318725 q = 1) : d320798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33547, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33547, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33548 q = 1) (hb : d318725 q = 1) : d320799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33548, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33548, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33665 q = 1) (hb : d318725 q = 1) : d320867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33665, d320867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33665, d320867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85681 (p : Pattern) (ha : d33669 p = 1) (hb : d318725 p = 1) : d320871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33596 q = 1) (hb : d318725 q = 1) : d320842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33596, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85673 q ha hb
    | true =>
      simp only [d33596, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33597 q = 1) (hb : d318725 q = 1) : d320843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33597, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33597, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33598 q = 1) (hb : d318725 q = 1) : d320844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33598, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33598, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33599 q = 1) (hb : d318725 q = 1) : d320845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33599, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33599, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33600 q = 1) (hb : d318725 q = 1) : d320846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33600, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33600, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33669 q = 1) (hb : d318725 q = 1) : d320871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33669, d320871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33669, d320871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85682 (p : Pattern) (ha : d33675 p = 1) (hb : d318725 p = 1) : d320874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85648 q ha hb
    | true =>
      simp only [d33503, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33648 q = 1) (hb : d318725 q = 1) : d320850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33648, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33648, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33649 q = 1) (hb : d318725 q = 1) : d320851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33649, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33649, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33650 q = 1) (hb : d318725 q = 1) : d320852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33650, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33650, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33675 q = 1) (hb : d318725 q = 1) : d320874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33675, d320874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33675, d320874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85683 (p : Pattern) (ha : d265997 p = 1) (hb : d318725 p = 1) : d320880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33540 q = 1) (hb : d318725 q = 1) : d320791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33540, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85662 q ha hb
    | true =>
      simp only [d33540, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85663 q ha hb
  have h2 (q : Pattern) (ha : d33541 q = 1) (hb : d318725 q = 1) : d320792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33541, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33541, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33542 q = 1) (hb : d318725 q = 1) : d320793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33542, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33542, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33543 q = 1) (hb : d318725 q = 1) : d320794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33543, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33543, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33550 q = 1) (hb : d318725 q = 1) : d320801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33550, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85664 q ha hb
    | true =>
      simp only [d33550, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85665 q ha hb
  have h6 (q : Pattern) (ha : d33551 q = 1) (hb : d318725 q = 1) : d320802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33551, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33551, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33552 q = 1) (hb : d318725 q = 1) : d320803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33552, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33552, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33602 q = 1) (hb : d318725 q = 1) : d320848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33602, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85674 q ha hb
    | true =>
      simp only [d33602, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85650 q ha hb
  have h9 (q : Pattern) (ha : d265988 q = 1) (hb : d318725 q = 1) : d320849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265988, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33652 q = 1) (hb : d318725 q = 1) : d320854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33652, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85675 q ha hb
    | true =>
      simp only [d33652, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33653 q = 1) (hb : d318725 q = 1) : d320855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33653, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33653, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265989 q = 1) (hb : d318725 q = 1) : d320856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265989, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265990 q = 1) (hb : d318725 q = 1) : d320857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265990, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265991 q = 1) (hb : d318725 q = 1) : d320858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265991, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33660 q = 1) (hb : d318725 q = 1) : d320862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33660, d320862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85677 q ha hb
    | true =>
      simp only [d33660, d320862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85678 q ha hb
  have h16 (q : Pattern) (ha : d33661 q = 1) (hb : d318725 q = 1) : d320863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33661, d320863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33661, d320863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33662 q = 1) (hb : d318725 q = 1) : d320864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33662, d320864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33662, d320864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33663 q = 1) (hb : d318725 q = 1) : d320865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33663, d320865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33663, d320865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33666 q = 1) (hb : d318725 q = 1) : d320868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33666, d320868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85679 q ha hb
    | true =>
      simp only [d33666, d320868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85680 q ha hb
  have h20 (q : Pattern) (ha : d33667 q = 1) (hb : d318725 q = 1) : d320869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33667, d320869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33667, d320869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d33668 q = 1) (hb : d318725 q = 1) : d320870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33668, d320870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33668, d320870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33670 q = 1) (hb : d318725 q = 1) : d320872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33670, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85681 q ha hb
    | true =>
      simp only [d33670, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85653 q ha hb
  have h23 (q : Pattern) (ha : d265993 q = 1) (hb : d318725 q = 1) : d320873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265993, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33676 q = 1) (hb : d318725 q = 1) : d320875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33676, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85682 q ha hb
    | true =>
      simp only [d33676, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d33677 q = 1) (hb : d318725 q = 1) : d320876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33677, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33677, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d265994 q = 1) (hb : d318725 q = 1) : d320877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d265994, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d265995 q = 1) (hb : d318725 q = 1) : d320878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d320878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265995, d320878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d265996 q = 1) (hb : d318725 q = 1) : d320879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d320879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265996, d320879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d265997 q = 1) (hb : d318725 q = 1) : d320880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d320880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265997, d320880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro85684 (p : Pattern) (ha : d266004 p = 1) (hb : d318725 p = 1) : d320900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33670 q = 1) (hb : d318725 q = 1) : d320872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33670, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85681 q ha hb
    | true =>
      simp only [d33670, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85653 q ha hb
  have h2 (q : Pattern) (ha : d265993 q = 1) (hb : d318725 q = 1) : d320873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265993, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33676 q = 1) (hb : d318725 q = 1) : d320875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33676, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85682 q ha hb
    | true =>
      simp only [d33676, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33677 q = 1) (hb : d318725 q = 1) : d320876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33677, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33677, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d318725 q = 1) : d320877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265994, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d318725 q = 1) : d320898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d320898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d320898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d318725 q = 1) : d320899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d320899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d320899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d318725 q = 1) : d320900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d320900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d320900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85685 (p : Pattern) (ha : d33723 p = 1) (hb : d318725 p = 1) : d320922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33709 q = 1) (hb : d318725 q = 1) : d320908 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33709, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33709, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
  have h2 (q : Pattern) (ha : d33567 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
    | true =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33710 q = 1) (hb : d318725 q = 1) : d320909 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33710, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33710, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33568 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33711 q = 1) (hb : d318725 q = 1) : d320910 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33711, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33711, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33712 q = 1) (hb : d318725 q = 1) : d320911 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33712, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33712, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33713 q = 1) (hb : d318725 q = 1) : d320912 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33713, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33713, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
  have h8 (q : Pattern) (ha : d33572 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
    | true =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33714 q = 1) (hb : d318725 q = 1) : d320913 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33714, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33714, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33573 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33715 q = 1) (hb : d318725 q = 1) : d320914 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33715, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33715, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33716 q = 1) (hb : d318725 q = 1) : d320915 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33716, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33716, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33717 q = 1) (hb : d318725 q = 1) : d320916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33717, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33717, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33718 q = 1) (hb : d318725 q = 1) : d320917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
  have h15 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33719 q = 1) (hb : d318725 q = 1) : d320918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33720 q = 1) (hb : d318725 q = 1) : d320919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33721 q = 1) (hb : d318725 q = 1) : d320920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33439 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
  have h21 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33440 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33441 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33442 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33722 q = 1) (hb : d318725 q = 1) : d320921 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33722, d320921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33722, d320921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d33723 q = 1) (hb : d318725 q = 1) : d320922 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33723, d320922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33723, d320922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro85686 (p : Pattern) (ha : d33727 p = 1) (hb : d318725 p = 1) : d320926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33439 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
  have h2 (q : Pattern) (ha : d33342 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85629 q ha hb
    | true =>
      simp only [d33342, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33440 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33440, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33343 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33343, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33441 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33441, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33442 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33442, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33443 q = 1) (hb : d318725 q = 1) : d320713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33443, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d318725 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33727 q = 1) (hb : d318725 q = 1) : d320926 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33727, d320926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33727, d320926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro85687 (p : Pattern) (ha : d33733 p = 1) (hb : d318725 p = 1) : d320932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33724 q = 1) (hb : d318725 q = 1) : d320923 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33724, d320923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85685 q ha hb
    | true =>
      simp only [d33724, d320923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85641 q ha hb
  have h2 (q : Pattern) (ha : d33725 q = 1) (hb : d318725 q = 1) : d320924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33725, d320924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33725, d320924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33726 q = 1) (hb : d318725 q = 1) : d320925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33726, d320925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33726, d320925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33728 q = 1) (hb : d318725 q = 1) : d320927 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33728, d320927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85641 q ha hb
    | true =>
      simp only [d33728, d320927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85686 q ha hb
  have h5 (q : Pattern) (ha : d33729 q = 1) (hb : d318725 q = 1) : d320928 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33729, d320928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33729, d320928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33730 q = 1) (hb : d318725 q = 1) : d320929 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33730, d320929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33730, d320929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33731 q = 1) (hb : d318725 q = 1) : d320930 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33731, d320930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33731, d320930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33445 q = 1) (hb : d318725 q = 1) : d320715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85641 q ha hb
    | true =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
  have h9 (q : Pattern) (ha : d33446 q = 1) (hb : d318725 q = 1) : d320716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33447 q = 1) (hb : d318725 q = 1) : d320717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d33270 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
    | true =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33271 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33272 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33448 q = 1) (hb : d318725 q = 1) : d320718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33732 q = 1) (hb : d318725 q = 1) : d320931 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33732, d320931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33732, d320931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33733 q = 1) (hb : d318725 q = 1) : d320932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33733, d320932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33733, d320932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro85688 (p : Pattern) (ha : d33738 p = 1) (hb : d318725 p = 1) : d320937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d318725 q = 1) : d320715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85641 q ha hb
    | true =>
      simp only [d33445, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d318725 q = 1) : d320716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d318725 q = 1) : d320717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33270 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85617 q ha hb
    | true =>
      simp only [d33270, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33271 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33272 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33448 q = 1) (hb : d318725 q = 1) : d320718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33736 q = 1) (hb : d318725 q = 1) : d320935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33736, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33736, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33737 q = 1) (hb : d318725 q = 1) : d320936 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33737, d320936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33737, d320936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33738 q = 1) (hb : d318725 q = 1) : d320937 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33738, d320937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33738, d320937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro85689 (p : Pattern) (ha : d33744 p = 1) (hb : d318725 p = 1) : d320943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33734 q = 1) (hb : d318725 q = 1) : d320933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33734, d320933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85687 q ha hb
    | true =>
      simp only [d33734, d320933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33735 q = 1) (hb : d318725 q = 1) : d320934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33735, d320934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33735, d320934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33739 q = 1) (hb : d318725 q = 1) : d320938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85688 q ha hb
    | true =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33740 q = 1) (hb : d318725 q = 1) : d320939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33741 q = 1) (hb : d318725 q = 1) : d320940 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33741, d320940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33741, d320940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33742 q = 1) (hb : d318725 q = 1) : d320941 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33742, d320941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33742, d320941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33743 q = 1) (hb : d318725 q = 1) : d320942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33743, d320942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33743, d320942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33744 q = 1) (hb : d318725 q = 1) : d320943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33744, d320943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33744, d320943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85690 (p : Pattern) (ha : d33752 p = 1) (hb : d318725 p = 1) : d320951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33739 q = 1) (hb : d318725 q = 1) : d320938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85688 q ha hb
    | true =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33740 q = 1) (hb : d318725 q = 1) : d320939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33747 q = 1) (hb : d318725 q = 1) : d320946 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33747, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85659 q ha hb
    | true =>
      simp only [d33747, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33748 q = 1) (hb : d318725 q = 1) : d320947 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33748, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33748, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33749 q = 1) (hb : d318725 q = 1) : d320948 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33749, d320948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33749, d320948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33750 q = 1) (hb : d318725 q = 1) : d320949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33750, d320949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33750, d320949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33751 q = 1) (hb : d318725 q = 1) : d320950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33751, d320950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33751, d320950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33752 q = 1) (hb : d318725 q = 1) : d320951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33752, d320951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33752, d320951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85691 (p : Pattern) (ha : d33791 p = 1) (hb : d318725 p = 1) : d320957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33739 q = 1) (hb : d318725 q = 1) : d320938 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85688 q ha hb
    | true =>
      simp only [d33739, d320938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33740 q = 1) (hb : d318725 q = 1) : d320939 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d320939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33788 q = 1) (hb : d318725 q = 1) : d320954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33788, d320954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33788, d320954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33789 q = 1) (hb : d318725 q = 1) : d320955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33789, d320955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33789, d320955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33790 q = 1) (hb : d318725 q = 1) : d320956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33790, d320956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33790, d320956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33791 q = 1) (hb : d318725 q = 1) : d320957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33791, d320957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33791, d320957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85692 (p : Pattern) (ha : d266014 p = 1) (hb : d318725 p = 1) : d320963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33753 q = 1) (hb : d318725 q = 1) : d320952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33753, d320952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85689 q ha hb
    | true =>
      simp only [d33753, d320952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85690 q ha hb
  have h2 (q : Pattern) (ha : d266010 q = 1) (hb : d318725 q = 1) : d320953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d320953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266010, d320953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33792 q = 1) (hb : d318725 q = 1) : d320958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33792, d320958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85691 q ha hb
    | true =>
      simp only [d33792, d320958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33793 q = 1) (hb : d318725 q = 1) : d320959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33793, d320959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33793, d320959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d318725 q = 1) : d320960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d320960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266011, d320960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d318725 q = 1) : d320961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d320961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d320961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d318725 q = 1) : d320962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d320962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d320962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d318725 q = 1) : d320963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d320963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d320963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85693 (p : Pattern) (ha : d266020 p = 1) (hb : d318725 p = 1) : d320980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33523 q = 1) (hb : d318725 q = 1) : d320774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33523, d320774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33523, d320774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85652 q ha hb
  have h2 (q : Pattern) (ha : d33524 q = 1) (hb : d318725 q = 1) : d320775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33524, d320775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33524, d320775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33533 q = 1) (hb : d318725 q = 1) : d320784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33533, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85652 q ha hb
    | true =>
      simp only [d33533, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85655 q ha hb
  have h4 (q : Pattern) (ha : d33534 q = 1) (hb : d318725 q = 1) : d320785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33534, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33534, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33535 q = 1) (hb : d318725 q = 1) : d320786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33535, d320786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33535, d320786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265998 q = 1) (hb : d318725 q = 1) : d320881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d320881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85676 q ha hb
    | true =>
      simp only [d265998, d320881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85683 q ha hb
  have h7 (q : Pattern) (ha : d33695 q = 1) (hb : d318725 q = 1) : d320894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33695, d320894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85656 q ha hb
    | true =>
      simp only [d33695, d320894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85657 q ha hb
  have h8 (q : Pattern) (ha : d265999 q = 1) (hb : d318725 q = 1) : d320895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d320895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265999, d320895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266000 q = 1) (hb : d318725 q = 1) : d320896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d320896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266000, d320896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d266001 q = 1) (hb : d318725 q = 1) : d320897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d320897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266001, d320897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266005 q = 1) (hb : d318725 q = 1) : d320901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d320901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266005, d320901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85684 q ha hb
  have h12 (q : Pattern) (ha : d33704 q = 1) (hb : d318725 q = 1) : d320903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33704, d320903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33704, d320903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85658 q ha hb
  have h13 (q : Pattern) (ha : d266006 q = 1) (hb : d318725 q = 1) : d320904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d320904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d266006, d320904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266007 q = 1) (hb : d318725 q = 1) : d320905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d320905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266007, d320905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d266008 q = 1) (hb : d318725 q = 1) : d320906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d320906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266008, d320906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d266009 q = 1) (hb : d318725 q = 1) : d320907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d320907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266009, d320907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266015 q = 1) (hb : d318725 q = 1) : d320964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d320964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266015, d320964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85692 q ha hb
  have h18 (q : Pattern) (ha : d33809 q = 1) (hb : d318725 q = 1) : d320975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33809, d320975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33809, d320975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85661 q ha hb
  have h19 (q : Pattern) (ha : d266016 q = 1) (hb : d318725 q = 1) : d320976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d320976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266016, d320976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d266017 q = 1) (hb : d318725 q = 1) : d320977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d320977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d266017, d320977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d266018 q = 1) (hb : d318725 q = 1) : d320978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d320978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d266018, d320978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d266019 q = 1) (hb : d318725 q = 1) : d320979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d320979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266019, d320979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d266020 q = 1) (hb : d318725 q = 1) : d320980 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d320980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266020, d320980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro85694 (p : Pattern) (ha : d266026 p = 1) (hb : d318725 p = 1) : d320986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d318725 q = 1) : d320981 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d320981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d320981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85693 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d318725 q = 1) : d320982 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d320982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d320982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d318725 q = 1) : d320983 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d320983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d320983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d318725 q = 1) : d320984 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d320984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d320984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d318725 q = 1) : d320985 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d320985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d320985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d318725 q = 1) : d320986 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d320986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d320986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85695 (p : Pattern) (ha : d33822 p = 1) (hb : d318725 p = 1) : d320988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d318725 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33218 q = 1) (hb : d318725 q = 1) : d320518 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33218, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33219 q = 1) (hb : d318725 q = 1) : d320519 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33219, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33822 q = 1) (hb : d318725 q = 1) : d320988 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33822, d320988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33822, d320988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85696 (p : Pattern) (ha : d33828 p = 1) (hb : d318725 p = 1) : d320994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33567 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
    | true =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33568 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33569 q = 1) (hb : d318725 q = 1) : d320815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33569, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33569, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33570 q = 1) (hb : d318725 q = 1) : d320816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33570, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33570, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33572 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
    | true =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33573 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33574 q = 1) (hb : d318725 q = 1) : d320820 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33574, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33574, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33575 q = 1) (hb : d318725 q = 1) : d320821 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33575, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33575, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33576 q = 1) (hb : d318725 q = 1) : d320822 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33576, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33576, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33582 q = 1) (hb : d318725 q = 1) : d320828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33583 q = 1) (hb : d318725 q = 1) : d320829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33825 q = 1) (hb : d318725 q = 1) : d320991 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33826 q = 1) (hb : d318725 q = 1) : d320992 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33827 q = 1) (hb : d318725 q = 1) : d320993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33827, d320993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33827, d320993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33828 q = 1) (hb : d318725 q = 1) : d320994 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33828, d320994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33828, d320994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85697 (p : Pattern) (ha : d33831 p = 1) (hb : d318725 p = 1) : d320997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
    | true =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d318725 q = 1) : d320635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d318725 q = 1) : d320636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33825 q = 1) (hb : d318725 q = 1) : d320991 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33826 q = 1) (hb : d318725 q = 1) : d320992 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33829 q = 1) (hb : d318725 q = 1) : d320995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33829, d320995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33829, d320995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33830 q = 1) (hb : d318725 q = 1) : d320996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33831 q = 1) (hb : d318725 q = 1) : d320997 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33831, d320997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33831, d320997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85698 (p : Pattern) (ha : d33835 p = 1) (hb : d318725 p = 1) : d321001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33825 q = 1) (hb : d318725 q = 1) : d320991 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33826 q = 1) (hb : d318725 q = 1) : d320992 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33830 q = 1) (hb : d318725 q = 1) : d320996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33835 q = 1) (hb : d318725 q = 1) : d321001 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33835, d321001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33835, d321001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85699 (p : Pattern) (ha : d33842 p = 1) (hb : d318725 p = 1) : d321008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33832 q = 1) (hb : d318725 q = 1) : d320998 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33832, d320998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85696 q ha hb
    | true =>
      simp only [d33832, d320998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85697 q ha hb
  have h2 (q : Pattern) (ha : d33833 q = 1) (hb : d318725 q = 1) : d320999 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33833, d320999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33833, d320999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33834 q = 1) (hb : d318725 q = 1) : d321000 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33834, d321000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33834, d321000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33836 q = 1) (hb : d318725 q = 1) : d321002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85697 q ha hb
    | true =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85698 q ha hb
  have h5 (q : Pattern) (ha : d33837 q = 1) (hb : d318725 q = 1) : d321003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33838 q = 1) (hb : d318725 q = 1) : d321004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33839 q = 1) (hb : d318725 q = 1) : d321005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33839, d321005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33839, d321005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33840 q = 1) (hb : d318725 q = 1) : d321006 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33840, d321006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33840, d321006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33841 q = 1) (hb : d318725 q = 1) : d321007 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33841, d321007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33841, d321007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33842 q = 1) (hb : d318725 q = 1) : d321008 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33842, d321008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33842, d321008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro85700 (p : Pattern) (ha : d33846 p = 1) (hb : d318725 p = 1) : d321012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33836 q = 1) (hb : d318725 q = 1) : d321002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85697 q ha hb
    | true =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85698 q ha hb
  have h2 (q : Pattern) (ha : d33837 q = 1) (hb : d318725 q = 1) : d321003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33838 q = 1) (hb : d318725 q = 1) : d321004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33840 q = 1) (hb : d318725 q = 1) : d321006 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33840, d321006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33840, d321006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33845 q = 1) (hb : d318725 q = 1) : d321011 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33845, d321011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33845, d321011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33846 q = 1) (hb : d318725 q = 1) : d321012 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33846, d321012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33846, d321012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85701 (p : Pattern) (ha : d33852 p = 1) (hb : d318725 p = 1) : d321018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d318725 q = 1) : d321016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33851 q = 1) (hb : d318725 q = 1) : d321017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33851, d321017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33851, d321017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33852 q = 1) (hb : d318725 q = 1) : d321018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33852, d321018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33852, d321018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85702 (p : Pattern) (ha : d33856 p = 1) (hb : d318725 p = 1) : d321022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d318725 q = 1) : d321020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33855 q = 1) (hb : d318725 q = 1) : d321021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33855, d321021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33855, d321021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33856 q = 1) (hb : d318725 q = 1) : d321022 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33856, d321022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33856, d321022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85703 (p : Pattern) (ha : d33862 p = 1) (hb : d318725 p = 1) : d321028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d318725 q = 1) : d321023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85701 q ha hb
    | true =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85702 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d318725 q = 1) : d321024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d318725 q = 1) : d321025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d318725 q = 1) : d321026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d318725 q = 1) : d321027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33862 q = 1) (hb : d318725 q = 1) : d321028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33862, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33862, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85704 (p : Pattern) (ha : d33865 p = 1) (hb : d318725 p = 1) : d321031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d318725 q = 1) : d321016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33851 q = 1) (hb : d318725 q = 1) : d321017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33851, d321017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33851, d321017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33865 q = 1) (hb : d318725 q = 1) : d321031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33865, d321031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33865, d321031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85705 (p : Pattern) (ha : d33866 p = 1) (hb : d318725 p = 1) : d321032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d318725 q = 1) : d321020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33855 q = 1) (hb : d318725 q = 1) : d321021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33855, d321021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33855, d321021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33866 q = 1) (hb : d318725 q = 1) : d321032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33866, d321032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33866, d321032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85706 (p : Pattern) (ha : d33872 p = 1) (hb : d318725 p = 1) : d321038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d318725 q = 1) : d321023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85701 q ha hb
    | true =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85702 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d318725 q = 1) : d321024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d318725 q = 1) : d321025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d318725 q = 1) : d321026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d318725 q = 1) : d321027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33867 q = 1) (hb : d318725 q = 1) : d321033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33867, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85704 q ha hb
    | true =>
      simp only [d33867, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85705 q ha hb
  have h7 (q : Pattern) (ha : d33868 q = 1) (hb : d318725 q = 1) : d321034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33868, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33868, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33869 q = 1) (hb : d318725 q = 1) : d321035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33869, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33869, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33870 q = 1) (hb : d318725 q = 1) : d321036 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33870, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33870, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33871 q = 1) (hb : d318725 q = 1) : d321037 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33871, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33871, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33872 q = 1) (hb : d318725 q = 1) : d321038 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33872, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33872, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85707 (p : Pattern) (ha : d34058 p = 1) (hb : d318725 p = 1) : d321149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d318725 q = 1) : d321023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85701 q ha hb
    | true =>
      simp only [d33857, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85702 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d318725 q = 1) : d321024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d318725 q = 1) : d321025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d318725 q = 1) : d321026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d318725 q = 1) : d321027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34053 q = 1) (hb : d318725 q = 1) : d321144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34053, d321144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85702 q ha hb
    | true =>
      simp only [d34053, d321144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34054 q = 1) (hb : d318725 q = 1) : d321145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34054, d321145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34054, d321145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34055 q = 1) (hb : d318725 q = 1) : d321146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34055, d321146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34055, d321146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34056 q = 1) (hb : d318725 q = 1) : d321147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34056, d321147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34056, d321147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34057 q = 1) (hb : d318725 q = 1) : d321148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34057, d321148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34057, d321148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34058 q = 1) (hb : d318725 q = 1) : d321149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34058, d321149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34058, d321149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85708 (p : Pattern) (ha : d34064 p = 1) (hb : d318725 p = 1) : d321155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34053 q = 1) (hb : d318725 q = 1) : d321144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34053, d321144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85702 q ha hb
    | true =>
      simp only [d34053, d321144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34054 q = 1) (hb : d318725 q = 1) : d321145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34054, d321145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34054, d321145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34055 q = 1) (hb : d318725 q = 1) : d321146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34055, d321146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34055, d321146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34056 q = 1) (hb : d318725 q = 1) : d321147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34056, d321147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34056, d321147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34057 q = 1) (hb : d318725 q = 1) : d321148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34057, d321148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34057, d321148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34059 q = 1) (hb : d318725 q = 1) : d321150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34059, d321150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85705 q ha hb
    | true =>
      simp only [d34059, d321150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34060 q = 1) (hb : d318725 q = 1) : d321151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34060, d321151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34060, d321151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34061 q = 1) (hb : d318725 q = 1) : d321152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34061, d321152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34061, d321152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34062 q = 1) (hb : d318725 q = 1) : d321153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34062, d321153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34062, d321153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34063 q = 1) (hb : d318725 q = 1) : d321154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34063, d321154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34063, d321154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34064 q = 1) (hb : d318725 q = 1) : d321155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34064, d321155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34064, d321155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85709 (p : Pattern) (ha : d34073 p = 1) (hb : d318725 p = 1) : d321164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34059 q = 1) (hb : d318725 q = 1) : d321150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34059, d321150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85705 q ha hb
    | true =>
      simp only [d34059, d321150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34060 q = 1) (hb : d318725 q = 1) : d321151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34060, d321151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34060, d321151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34061 q = 1) (hb : d318725 q = 1) : d321152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34061, d321152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34061, d321152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34062 q = 1) (hb : d318725 q = 1) : d321153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34062, d321153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34062, d321153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34063 q = 1) (hb : d318725 q = 1) : d321154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34063, d321154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34063, d321154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34073 q = 1) (hb : d318725 q = 1) : d321164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34073, d321164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34073, d321164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85710 (p : Pattern) (ha : d34110 p = 1) (hb : d318725 p = 1) : d321201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d318725 q = 1) : d320704 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85628 q ha hb
    | true =>
      simp only [d33334, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d318725 q = 1) : d320705 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d318725 q = 1) : d320706 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d318725 q = 1) : d320707 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34094 q = 1) (hb : d318725 q = 1) : d321185 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
  have h8 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34095 q = 1) (hb : d318725 q = 1) : d321186 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34096 q = 1) (hb : d318725 q = 1) : d321187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34097 q = 1) (hb : d318725 q = 1) : d321188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34109 q = 1) (hb : d318725 q = 1) : d321200 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34109, d321200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34109, d321200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34103 q = 1) (hb : d318725 q = 1) : d321194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d34110 q = 1) (hb : d318725 q = 1) : d321201 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34110, d321201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34110, d321201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85711 (p : Pattern) (ha : d34114 p = 1) (hb : d318725 p = 1) : d321205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34094 q = 1) (hb : d318725 q = 1) : d321185 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
  have h2 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34095 q = 1) (hb : d318725 q = 1) : d321186 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34096 q = 1) (hb : d318725 q = 1) : d321187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34097 q = 1) (hb : d318725 q = 1) : d321188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34103 q = 1) (hb : d318725 q = 1) : d321194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34114 q = 1) (hb : d318725 q = 1) : d321205 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34114, d321205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34114, d321205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85712 (p : Pattern) (ha : d34133 p = 1) (hb : d318725 p = 1) : d321224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34115 q = 1) (hb : d318725 q = 1) : d321206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85710 q ha hb
    | true =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85711 q ha hb
  have h2 (q : Pattern) (ha : d34116 q = 1) (hb : d318725 q = 1) : d321207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34117 q = 1) (hb : d318725 q = 1) : d321208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34123 q = 1) (hb : d318725 q = 1) : d321214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34123, d321214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34123, d321214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34132 q = 1) (hb : d318725 q = 1) : d321223 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34132, d321223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34132, d321223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34133 q = 1) (hb : d318725 q = 1) : d321224 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34133, d321224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34133, d321224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85713 (p : Pattern) (ha : d34204 p = 1) (hb : d318725 p = 1) : d321247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34134 q = 1) (hb : d318725 q = 1) : d321225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34134, d321225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85712 q ha hb
    | true =>
      simp only [d34134, d321225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34135 q = 1) (hb : d318725 q = 1) : d321226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34135, d321226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34135, d321226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34201 q = 1) (hb : d318725 q = 1) : d321244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34201, d321244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34201, d321244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34202 q = 1) (hb : d318725 q = 1) : d321245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34202, d321245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34202, d321245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34203 q = 1) (hb : d318725 q = 1) : d321246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34203, d321246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34203, d321246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34204 q = 1) (hb : d318725 q = 1) : d321247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34204, d321247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34204, d321247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85714 (p : Pattern) (ha : d34210 p = 1) (hb : d318725 p = 1) : d321253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34205 q = 1) (hb : d318725 q = 1) : d321248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34205, d321248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85713 q ha hb
    | true =>
      simp only [d34205, d321248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34206 q = 1) (hb : d318725 q = 1) : d321249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34206, d321249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34206, d321249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34207 q = 1) (hb : d318725 q = 1) : d321250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34207, d321250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34207, d321250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34208 q = 1) (hb : d318725 q = 1) : d321251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34208, d321251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34208, d321251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34209 q = 1) (hb : d318725 q = 1) : d321252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34209, d321252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34209, d321252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34210 q = 1) (hb : d318725 q = 1) : d321253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34210, d321253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34210, d321253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85715 (p : Pattern) (ha : d33877 p = 1) (hb : d318725 p = 1) : d321043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d318725 q = 1) : d321016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33876 q = 1) (hb : d318725 q = 1) : d321042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33876, d321042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33876, d321042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33877 q = 1) (hb : d318725 q = 1) : d321043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33877, d321043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33877, d321043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85716 (p : Pattern) (ha : d33879 p = 1) (hb : d318725 p = 1) : d321045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d318725 q = 1) : d321020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33878 q = 1) (hb : d318725 q = 1) : d321044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33878, d321044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33878, d321044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33879 q = 1) (hb : d318725 q = 1) : d321045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33879, d321045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33879, d321045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85717 (p : Pattern) (ha : d33886 p = 1) (hb : d318725 p = 1) : d321052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33884 q = 1) (hb : d318725 q = 1) : d321050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33884, d321050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33884, d321050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33885 q = 1) (hb : d318725 q = 1) : d321051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33885, d321051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33885, d321051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33886 q = 1) (hb : d318725 q = 1) : d321052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33886, d321052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33886, d321052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85718 (p : Pattern) (ha : d33889 p = 1) (hb : d318725 p = 1) : d321055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33887 q = 1) (hb : d318725 q = 1) : d321053 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33887, d321053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33887, d321053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33888 q = 1) (hb : d318725 q = 1) : d321054 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33888, d321054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33888, d321054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33889 q = 1) (hb : d318725 q = 1) : d321055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33889, d321055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33889, d321055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85719 (p : Pattern) (ha : d33894 p = 1) (hb : d318725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d528 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d33553 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33553, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33553, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d825 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d825, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5121 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5121, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5121, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h16 (q : Pattern) (ha : d33894 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro85720 (p : Pattern) (ha : d33897 p = 1) (hb : d318725 p = 1) : d321059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1520 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1520, d318724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d33554 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33554, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33554, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13 q = 1) (hb : d128 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d13 q = 1) (hb : d129 q = 1) : d44881 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d129, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d534 q = 1) (hb : d318724 q = 1) : d45231 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d318724, d45231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d534, d318724, d45231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h17 (q : Pattern) (ha : d33559 q = 1) (hb : d318725 q = 1) : d320805 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33559, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33559, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h18 (q : Pattern) (ha : d33897 q = 1) (hb : d318725 q = 1) : d321059 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33897, d321059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33897, d321059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85721 (p : Pattern) (ha : d33906 p = 1) (hb : d318725 p = 1) : d321068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85666 q ha hb
    | true =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33557 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33893 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33895 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85719 q ha hb
    | true =>
      simp only [d33895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33896 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33898 q = 1) (hb : d318725 q = 1) : d321060 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33898, d321060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85720 q ha hb
    | true =>
      simp only [d33898, d321060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33899 q = 1) (hb : d318725 q = 1) : d321061 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33899, d321061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33899, d321061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33900 q = 1) (hb : d318725 q = 1) : d321062 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33900, d321062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33900, d321062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33901 q = 1) (hb : d318725 q = 1) : d321063 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33901, d321063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33901, d321063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33902 q = 1) (hb : d318725 q = 1) : d321064 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33902, d321064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33902, d321064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33558 q = 1) (hb : d318725 q = 1) : d320804 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33903 q = 1) (hb : d318725 q = 1) : d321065 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33903, d321065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33903, d321065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33904 q = 1) (hb : d318725 q = 1) : d321066 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33904, d321066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33904, d321066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d33905 q = 1) (hb : d318725 q = 1) : d321067 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33905, d321067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d33905, d321067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d33906 q = 1) (hb : d318725 q = 1) : d321068 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33906, d321068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33906, d321068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85722 (p : Pattern) (ha : d33911 p = 1) (hb : d318725 p = 1) : d276432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d128 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d129 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310 q = 1) (hb : d318724 q = 1) : d44996 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d318724, d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33326 q = 1) (hb : d318725 q = 1) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33326, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13 q = 1) (hb : d1519 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d1540 q = 1) (hb : d318724 q = 1) : d45587 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1540, d318724, d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1540, d318724, d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1541 q = 1) (hb : d318725 q = 1) : d46472 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1541, d318725, d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1541, d318725, d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d33911 q = 1) (hb : d318725 q = 1) : d276432 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33911, d276432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33911, d276432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro85723 (p : Pattern) (ha : d33917 p = 1) (hb : d318725 p = 1) : d321078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85666 q ha hb
    | true =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33557 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33328 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85627 q ha hb
    | true =>
      simp only [d33328, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33329 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33329, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33558 q = 1) (hb : d318725 q = 1) : d320804 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33558, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33561 q = 1) (hb : d318725 q = 1) : d320807 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33561, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85667 q ha hb
    | true =>
      simp only [d33561, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33562 q = 1) (hb : d318725 q = 1) : d320808 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33562, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33562, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33563 q = 1) (hb : d318725 q = 1) : d320809 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33563, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33563, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33564 q = 1) (hb : d318725 q = 1) : d320810 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33564, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33564, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33565 q = 1) (hb : d318725 q = 1) : d320811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33565, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33565, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33912 q = 1) (hb : d318725 q = 1) : d321073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33912, d321073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85722 q ha hb
    | true =>
      simp only [d33912, d321073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33913 q = 1) (hb : d318725 q = 1) : d321074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33913, d321074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33913, d321074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33914 q = 1) (hb : d318725 q = 1) : d321075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33914, d321075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33914, d321075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d33915 q = 1) (hb : d318725 q = 1) : d321076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33915, d321076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33915, d321076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d33916 q = 1) (hb : d318725 q = 1) : d321077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33916, d321077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33916, d321077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33917 q = 1) (hb : d318725 q = 1) : d321078 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33917, d321078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33917, d321078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro85724 (p : Pattern) (ha : d33926 p = 1) (hb : d318725 p = 1) : d321087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85666 q ha hb
    | true =>
      simp only [d33556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33557 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33912 q = 1) (hb : d318725 q = 1) : d321073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33912, d321073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85722 q ha hb
    | true =>
      simp only [d33912, d321073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33913 q = 1) (hb : d318725 q = 1) : d321074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33913, d321074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33913, d321074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33923 q = 1) (hb : d318725 q = 1) : d321084 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33923, d321084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33923, d321084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33924 q = 1) (hb : d318725 q = 1) : d321085 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33924, d321085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33924, d321085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33925 q = 1) (hb : d318725 q = 1) : d321086 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33925, d321086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33925, d321086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33215 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85608 q ha hb
    | true =>
      simp only [d33215, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33216 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33216, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33914 q = 1) (hb : d318725 q = 1) : d321075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33914, d321075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33914, d321075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33915 q = 1) (hb : d318725 q = 1) : d321076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33915, d321076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33915, d321076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33916 q = 1) (hb : d318725 q = 1) : d321077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33916, d321077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33916, d321077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33926 q = 1) (hb : d318725 q = 1) : d321087 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33926, d321087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33926, d321087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro85725 (p : Pattern) (ha : d33932 p = 1) (hb : d318725 p = 1) : d321093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33907 q = 1) (hb : d318725 q = 1) : d321069 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33907, d321069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85721 q ha hb
    | true =>
      simp only [d33907, d321069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33908 q = 1) (hb : d318725 q = 1) : d321070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33908, d321070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33908, d321070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33909 q = 1) (hb : d318725 q = 1) : d321071 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33909, d321071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33909, d321071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33910 q = 1) (hb : d318725 q = 1) : d321072 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33910, d321072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33910, d321072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33918 q = 1) (hb : d318725 q = 1) : d321079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33918, d321079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85723 q ha hb
    | true =>
      simp only [d33918, d321079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33919 q = 1) (hb : d318725 q = 1) : d321080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33919, d321080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33919, d321080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33920 q = 1) (hb : d318725 q = 1) : d321081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33920, d321081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33920, d321081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33921 q = 1) (hb : d318725 q = 1) : d321082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33921, d321082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33921, d321082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33922 q = 1) (hb : d318725 q = 1) : d321083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33922, d321083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33922, d321083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33927 q = 1) (hb : d318725 q = 1) : d321088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33927, d321088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85724 q ha hb
    | true =>
      simp only [d33927, d321088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33928 q = 1) (hb : d318725 q = 1) : d321089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33928, d321089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33928, d321089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33929 q = 1) (hb : d318725 q = 1) : d321090 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33929, d321090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33929, d321090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33930 q = 1) (hb : d318725 q = 1) : d321091 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33930, d321091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33930, d321091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33582 q = 1) (hb : d318725 q = 1) : d320828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33583 q = 1) (hb : d318725 q = 1) : d320829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33931 q = 1) (hb : d318725 q = 1) : d321092 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33931, d321092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33931, d321092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33932 q = 1) (hb : d318725 q = 1) : d321093 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33932, d321093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33932, d321093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro85726 (p : Pattern) (ha : d33936 p = 1) (hb : d318725 p = 1) : d321097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33582 q = 1) (hb : d318725 q = 1) : d320828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33583 q = 1) (hb : d318725 q = 1) : d320829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33583, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33825 q = 1) (hb : d318725 q = 1) : d320991 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d320991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33826 q = 1) (hb : d318725 q = 1) : d320992 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33826, d320992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33827 q = 1) (hb : d318725 q = 1) : d320993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33827, d320993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33827, d320993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33830 q = 1) (hb : d318725 q = 1) : d320996 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33830, d320996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33936 q = 1) (hb : d318725 q = 1) : d321097 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33936, d321097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33936, d321097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro85727 (p : Pattern) (ha : d33942 p = 1) (hb : d318725 p = 1) : d321103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33933 q = 1) (hb : d318725 q = 1) : d321094 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33933, d321094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85725 q ha hb
    | true =>
      simp only [d33933, d321094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85696 q ha hb
  have h2 (q : Pattern) (ha : d33934 q = 1) (hb : d318725 q = 1) : d321095 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33934, d321095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33934, d321095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33935 q = 1) (hb : d318725 q = 1) : d321096 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33935, d321096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33935, d321096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33937 q = 1) (hb : d318725 q = 1) : d321098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33937, d321098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85696 q ha hb
    | true =>
      simp only [d33937, d321098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85726 q ha hb
  have h5 (q : Pattern) (ha : d33938 q = 1) (hb : d318725 q = 1) : d321099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33938, d321099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33938, d321099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33939 q = 1) (hb : d318725 q = 1) : d321100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33939, d321100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33939, d321100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33940 q = 1) (hb : d318725 q = 1) : d321101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33940, d321101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33940, d321101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33832 q = 1) (hb : d318725 q = 1) : d320998 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33832, d320998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85696 q ha hb
    | true =>
      simp only [d33832, d320998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85697 q ha hb
  have h9 (q : Pattern) (ha : d33833 q = 1) (hb : d318725 q = 1) : d320999 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33833, d320999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33833, d320999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33834 q = 1) (hb : d318725 q = 1) : d321000 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33834, d321000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33834, d321000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33836 q = 1) (hb : d318725 q = 1) : d321002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85697 q ha hb
    | true =>
      simp only [d33836, d321002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85698 q ha hb
  have h12 (q : Pattern) (ha : d33837 q = 1) (hb : d318725 q = 1) : d321003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d321003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33838 q = 1) (hb : d318725 q = 1) : d321004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d321004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33839 q = 1) (hb : d318725 q = 1) : d321005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33839, d321005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33839, d321005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33941 q = 1) (hb : d318725 q = 1) : d321102 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33941, d321102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33941, d321102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33942 q = 1) (hb : d318725 q = 1) : d321103 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33942, d321103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33942, d321103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro85728 (p : Pattern) (ha : d33948 p = 1) (hb : d318725 p = 1) : d321109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33943 q = 1) (hb : d318725 q = 1) : d321104 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33943, d321104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85727 q ha hb
    | true =>
      simp only [d33943, d321104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33944 q = 1) (hb : d318725 q = 1) : d321105 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33944, d321105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33944, d321105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33945 q = 1) (hb : d318725 q = 1) : d321106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33945, d321106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33945, d321106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33946 q = 1) (hb : d318725 q = 1) : d321107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33946, d321107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33946, d321107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33947 q = 1) (hb : d318725 q = 1) : d321108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33947, d321108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33947, d321108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33948 q = 1) (hb : d318725 q = 1) : d321109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33948, d321109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33948, d321109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85729 (p : Pattern) (ha : d34021 p = 1) (hb : d318725 p = 1) : d321115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34018 q = 1) (hb : d318725 q = 1) : d321112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34018, d321112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34018, d321112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34019 q = 1) (hb : d318725 q = 1) : d321113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34019, d321113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34019, d321113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34020 q = 1) (hb : d318725 q = 1) : d321114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34020, d321114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34020, d321114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34021 q = 1) (hb : d318725 q = 1) : d321115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34021, d321115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34021, d321115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro85730 (p : Pattern) (ha : d266032 p = 1) (hb : d318725 p = 1) : d321121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33880 q = 1) (hb : d318725 q = 1) : d321046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33880, d321046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85715 q ha hb
    | true =>
      simp only [d33880, d321046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85716 q ha hb
  have h2 (q : Pattern) (ha : d33881 q = 1) (hb : d318725 q = 1) : d321047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33881, d321047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33881, d321047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33882 q = 1) (hb : d318725 q = 1) : d321048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33882, d321048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33882, d321048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33883 q = 1) (hb : d318725 q = 1) : d321049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33883, d321049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33883, d321049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33890 q = 1) (hb : d318725 q = 1) : d321056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33890, d321056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85717 q ha hb
    | true =>
      simp only [d33890, d321056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85718 q ha hb
  have h6 (q : Pattern) (ha : d33891 q = 1) (hb : d318725 q = 1) : d321057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33891, d321057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33891, d321057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33892 q = 1) (hb : d318725 q = 1) : d321058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33892, d321058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33892, d321058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33949 q = 1) (hb : d318725 q = 1) : d321110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33949, d321110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85728 q ha hb
    | true =>
      simp only [d33949, d321110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85701 q ha hb
  have h9 (q : Pattern) (ha : d266028 q = 1) (hb : d318725 q = 1) : d321111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d321111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266028, d321111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d34022 q = 1) (hb : d318725 q = 1) : d321116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34022, d321116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85729 q ha hb
    | true =>
      simp only [d34022, d321116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34023 q = 1) (hb : d318725 q = 1) : d321117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34023, d321117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34023, d321117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d266029 q = 1) (hb : d318725 q = 1) : d321118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d321118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266029, d321118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266030 q = 1) (hb : d318725 q = 1) : d321119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d321119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266030, d321119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266031 q = 1) (hb : d318725 q = 1) : d321120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d321120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266031, d321120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266032 q = 1) (hb : d318725 q = 1) : d321121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d321121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d321121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85731 (p : Pattern) (ha : d34028 p = 1) (hb : d318725 p = 1) : d321122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d318725 q = 1) : d321016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d321016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33876 q = 1) (hb : d318725 q = 1) : d321042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33876, d321042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33876, d321042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34028 q = 1) (hb : d318725 q = 1) : d321122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34028, d321122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34028, d321122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85732 (p : Pattern) (ha : d34029 p = 1) (hb : d318725 p = 1) : d321123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d318725 q = 1) : d321020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d321020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33878 q = 1) (hb : d318725 q = 1) : d321044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33878, d321044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33878, d321044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34029 q = 1) (hb : d318725 q = 1) : d321123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34029, d321123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34029, d321123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85733 (p : Pattern) (ha : d34034 p = 1) (hb : d318725 p = 1) : d321128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d318725 q = 1) : d321015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d321015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33884 q = 1) (hb : d318725 q = 1) : d321050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33884, d321050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33884, d321050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33885 q = 1) (hb : d318725 q = 1) : d321051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33885, d321051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33885, d321051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34034 q = 1) (hb : d318725 q = 1) : d321128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34034, d321128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34034, d321128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85734 (p : Pattern) (ha : d34035 p = 1) (hb : d318725 p = 1) : d321129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d318725 q = 1) : d321013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85700 q ha hb
    | true =>
      simp only [d33847, d321013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d318725 q = 1) : d321014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d321014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d318725 q = 1) : d321019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d321019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33887 q = 1) (hb : d318725 q = 1) : d321053 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33887, d321053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33887, d321053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33888 q = 1) (hb : d318725 q = 1) : d321054 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33888, d321054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33888, d321054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34035 q = 1) (hb : d318725 q = 1) : d321129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34035, d321129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34035, d321129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85735 (p : Pattern) (ha : d34039 p = 1) (hb : d318725 p = 1) : d321133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33943 q = 1) (hb : d318725 q = 1) : d321104 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33943, d321104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85727 q ha hb
    | true =>
      simp only [d33943, d321104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33944 q = 1) (hb : d318725 q = 1) : d321105 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33944, d321105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33944, d321105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33945 q = 1) (hb : d318725 q = 1) : d321106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33945, d321106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33945, d321106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33946 q = 1) (hb : d318725 q = 1) : d321107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33946, d321107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33946, d321107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33947 q = 1) (hb : d318725 q = 1) : d321108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33947, d321108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33947, d321108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34039 q = 1) (hb : d318725 q = 1) : d321133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34039, d321133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34039, d321133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85736 (p : Pattern) (ha : d34045 p = 1) (hb : d318725 p = 1) : d321136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d318725 q = 1) : d321009 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85699 q ha hb
    | true =>
      simp only [d33843, d321009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d318725 q = 1) : d321010 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d321010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34018 q = 1) (hb : d318725 q = 1) : d321112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34018, d321112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34018, d321112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34019 q = 1) (hb : d318725 q = 1) : d321113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34019, d321113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34019, d321113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34020 q = 1) (hb : d318725 q = 1) : d321114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34020, d321114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34020, d321114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34045 q = 1) (hb : d318725 q = 1) : d321136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34045, d321136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34045, d321136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85737 (p : Pattern) (ha : d266037 p = 1) (hb : d318725 p = 1) : d321142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33880 q = 1) (hb : d318725 q = 1) : d321046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33880, d321046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85715 q ha hb
    | true =>
      simp only [d33880, d321046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85716 q ha hb
  have h2 (q : Pattern) (ha : d33881 q = 1) (hb : d318725 q = 1) : d321047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33881, d321047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33881, d321047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33882 q = 1) (hb : d318725 q = 1) : d321048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33882, d321048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33882, d321048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33883 q = 1) (hb : d318725 q = 1) : d321049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33883, d321049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33883, d321049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33890 q = 1) (hb : d318725 q = 1) : d321056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33890, d321056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85717 q ha hb
    | true =>
      simp only [d33890, d321056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85718 q ha hb
  have h6 (q : Pattern) (ha : d33891 q = 1) (hb : d318725 q = 1) : d321057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33891, d321057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33891, d321057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33892 q = 1) (hb : d318725 q = 1) : d321058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33892, d321058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33892, d321058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33949 q = 1) (hb : d318725 q = 1) : d321110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33949, d321110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85728 q ha hb
    | true =>
      simp only [d33949, d321110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85701 q ha hb
  have h9 (q : Pattern) (ha : d266028 q = 1) (hb : d318725 q = 1) : d321111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d321111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266028, d321111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d34022 q = 1) (hb : d318725 q = 1) : d321116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34022, d321116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85729 q ha hb
    | true =>
      simp only [d34022, d321116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34023 q = 1) (hb : d318725 q = 1) : d321117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34023, d321117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34023, d321117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d266029 q = 1) (hb : d318725 q = 1) : d321118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d321118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266029, d321118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266030 q = 1) (hb : d318725 q = 1) : d321119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d321119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266030, d321119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266031 q = 1) (hb : d318725 q = 1) : d321120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d321120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266031, d321120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d34030 q = 1) (hb : d318725 q = 1) : d321124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34030, d321124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85731 q ha hb
    | true =>
      simp only [d34030, d321124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85732 q ha hb
  have h16 (q : Pattern) (ha : d34031 q = 1) (hb : d318725 q = 1) : d321125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34031, d321125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34031, d321125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d34032 q = 1) (hb : d318725 q = 1) : d321126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34032, d321126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d34032, d321126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d34033 q = 1) (hb : d318725 q = 1) : d321127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34033, d321127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34033, d321127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d34036 q = 1) (hb : d318725 q = 1) : d321130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34036, d321130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85733 q ha hb
    | true =>
      simp only [d34036, d321130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85734 q ha hb
  have h20 (q : Pattern) (ha : d34037 q = 1) (hb : d318725 q = 1) : d321131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34037, d321131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34037, d321131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d34038 q = 1) (hb : d318725 q = 1) : d321132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34038, d321132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d34038, d321132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d34040 q = 1) (hb : d318725 q = 1) : d321134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34040, d321134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85735 q ha hb
    | true =>
      simp only [d34040, d321134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85704 q ha hb
  have h23 (q : Pattern) (ha : d266033 q = 1) (hb : d318725 q = 1) : d321135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d321135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d266033, d321135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d34046 q = 1) (hb : d318725 q = 1) : d321137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34046, d321137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85736 q ha hb
    | true =>
      simp only [d34046, d321137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d34047 q = 1) (hb : d318725 q = 1) : d321138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34047, d321138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d34047, d321138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d266034 q = 1) (hb : d318725 q = 1) : d321139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d321139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d266034, d321139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d266035 q = 1) (hb : d318725 q = 1) : d321140 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d321140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266035, d321140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d266036 q = 1) (hb : d318725 q = 1) : d321141 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d321141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d266036, d321141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d266037 q = 1) (hb : d318725 q = 1) : d321142 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d321142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266037, d321142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro85738 (p : Pattern) (ha : d266044 p = 1) (hb : d318725 p = 1) : d321162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34040 q = 1) (hb : d318725 q = 1) : d321134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34040, d321134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85735 q ha hb
    | true =>
      simp only [d34040, d321134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85704 q ha hb
  have h2 (q : Pattern) (ha : d266033 q = 1) (hb : d318725 q = 1) : d321135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d321135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266033, d321135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34046 q = 1) (hb : d318725 q = 1) : d321137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34046, d321137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85736 q ha hb
    | true =>
      simp only [d34046, d321137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34047 q = 1) (hb : d318725 q = 1) : d321138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34047, d321138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34047, d321138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d318725 q = 1) : d321139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d321139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266034, d321139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d318725 q = 1) : d321160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d321160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d321160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d318725 q = 1) : d321161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d321161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d321161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d318725 q = 1) : d321162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d321162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d321162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85739 (p : Pattern) (ha : d34093 p = 1) (hb : d318725 p = 1) : d321184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34079 q = 1) (hb : d318725 q = 1) : d321170 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34079, d321170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34079, d321170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85721 q ha hb
  have h2 (q : Pattern) (ha : d33907 q = 1) (hb : d318725 q = 1) : d321069 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33907, d321069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85721 q ha hb
    | true =>
      simp only [d33907, d321069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34080 q = 1) (hb : d318725 q = 1) : d321171 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34080, d321171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34080, d321171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33908 q = 1) (hb : d318725 q = 1) : d321070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33908, d321070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33908, d321070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34081 q = 1) (hb : d318725 q = 1) : d321172 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34081, d321172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34081, d321172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34082 q = 1) (hb : d318725 q = 1) : d321173 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34082, d321173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34082, d321173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34083 q = 1) (hb : d318725 q = 1) : d321174 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34083, d321174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34083, d321174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85723 q ha hb
  have h8 (q : Pattern) (ha : d33918 q = 1) (hb : d318725 q = 1) : d321079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33918, d321079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85723 q ha hb
    | true =>
      simp only [d33918, d321079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34084 q = 1) (hb : d318725 q = 1) : d321175 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34084, d321175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34084, d321175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33919 q = 1) (hb : d318725 q = 1) : d321080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33919, d321080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33919, d321080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34085 q = 1) (hb : d318725 q = 1) : d321176 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34085, d321176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34085, d321176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34086 q = 1) (hb : d318725 q = 1) : d321177 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34086, d321177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34086, d321177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34087 q = 1) (hb : d318725 q = 1) : d321178 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34087, d321178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34087, d321178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34088 q = 1) (hb : d318725 q = 1) : d321179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34088, d321179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34088, d321179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85724 q ha hb
  have h15 (q : Pattern) (ha : d33927 q = 1) (hb : d318725 q = 1) : d321088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33927, d321088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85724 q ha hb
    | true =>
      simp only [d33927, d321088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d34089 q = 1) (hb : d318725 q = 1) : d321180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34089, d321180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d34089, d321180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33928 q = 1) (hb : d318725 q = 1) : d321089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33928, d321089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33928, d321089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d34090 q = 1) (hb : d318725 q = 1) : d321181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34090, d321181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d34090, d321181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d34091 q = 1) (hb : d318725 q = 1) : d321182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34091, d321182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d34091, d321182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33718 q = 1) (hb : d318725 q = 1) : d320917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
  have h21 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33719 q = 1) (hb : d318725 q = 1) : d320918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33720 q = 1) (hb : d318725 q = 1) : d320919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33721 q = 1) (hb : d318725 q = 1) : d320920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d34092 q = 1) (hb : d318725 q = 1) : d321183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34092, d321183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d34092, d321183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d34093 q = 1) (hb : d318725 q = 1) : d321184 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34093, d321184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34093, d321184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro85740 (p : Pattern) (ha : d34099 p = 1) (hb : d318725 p = 1) : d321190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33709 q = 1) (hb : d318725 q = 1) : d320908 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33709, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33709, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
  have h2 (q : Pattern) (ha : d33567 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85668 q ha hb
    | true =>
      simp only [d33567, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33710 q = 1) (hb : d318725 q = 1) : d320909 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33710, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33710, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33568 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33568, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33711 q = 1) (hb : d318725 q = 1) : d320910 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33711, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33711, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33712 q = 1) (hb : d318725 q = 1) : d320911 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33712, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33712, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33713 q = 1) (hb : d318725 q = 1) : d320912 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33713, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33713, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
  have h8 (q : Pattern) (ha : d33572 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85669 q ha hb
    | true =>
      simp only [d33572, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33714 q = 1) (hb : d318725 q = 1) : d320913 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33714, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33714, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33573 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33573, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33715 q = 1) (hb : d318725 q = 1) : d320914 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33715, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33715, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33716 q = 1) (hb : d318725 q = 1) : d320915 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33716, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33716, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33717 q = 1) (hb : d318725 q = 1) : d320916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33717, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33717, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33718 q = 1) (hb : d318725 q = 1) : d320917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
  have h15 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33719 q = 1) (hb : d318725 q = 1) : d320918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33720 q = 1) (hb : d318725 q = 1) : d320919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33721 q = 1) (hb : d318725 q = 1) : d320920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d34094 q = 1) (hb : d318725 q = 1) : d321185 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
  have h21 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d34095 q = 1) (hb : d318725 q = 1) : d321186 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d34096 q = 1) (hb : d318725 q = 1) : d321187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d34097 q = 1) (hb : d318725 q = 1) : d321188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d34098 q = 1) (hb : d318725 q = 1) : d321189 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34098, d321189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d34098, d321189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d34099 q = 1) (hb : d318725 q = 1) : d321190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34099, d321190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34099, d321190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro85741 (p : Pattern) (ha : d34104 p = 1) (hb : d318725 p = 1) : d321195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33718 q = 1) (hb : d318725 q = 1) : d320917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
  have h2 (q : Pattern) (ha : d33580 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85670 q ha hb
    | true =>
      simp only [d33580, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33719 q = 1) (hb : d318725 q = 1) : d320918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33719, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33581 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33581, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33720 q = 1) (hb : d318725 q = 1) : d320919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33720, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33721 q = 1) (hb : d318725 q = 1) : d320920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33721, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34094 q = 1) (hb : d318725 q = 1) : d321185 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d321185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
  have h8 (q : Pattern) (ha : d33823 q = 1) (hb : d318725 q = 1) : d320989 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85695 q ha hb
    | true =>
      simp only [d33823, d320989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34095 q = 1) (hb : d318725 q = 1) : d321186 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34095, d321186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33824 q = 1) (hb : d318725 q = 1) : d320990 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33824, d320990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34096 q = 1) (hb : d318725 q = 1) : d321187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34096, d321187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34097 q = 1) (hb : d318725 q = 1) : d321188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34097, d321188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34098 q = 1) (hb : d318725 q = 1) : d321189 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34098, d321189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34098, d321189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34103 q = 1) (hb : d318725 q = 1) : d321194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d34103, d321194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d34104 q = 1) (hb : d318725 q = 1) : d321195 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34104, d321195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34104, d321195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro85742 (p : Pattern) (ha : d34120 p = 1) (hb : d318725 p = 1) : d321211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34100 q = 1) (hb : d318725 q = 1) : d321191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34100, d321191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85739 q ha hb
    | true =>
      simp only [d34100, d321191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85740 q ha hb
  have h2 (q : Pattern) (ha : d34101 q = 1) (hb : d318725 q = 1) : d321192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34101, d321192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34101, d321192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34102 q = 1) (hb : d318725 q = 1) : d321193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34102, d321193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34102, d321193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34105 q = 1) (hb : d318725 q = 1) : d321196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34105, d321196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85740 q ha hb
    | true =>
      simp only [d34105, d321196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85741 q ha hb
  have h5 (q : Pattern) (ha : d34106 q = 1) (hb : d318725 q = 1) : d321197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34106, d321197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34106, d321197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34107 q = 1) (hb : d318725 q = 1) : d321198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34107, d321198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34107, d321198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34108 q = 1) (hb : d318725 q = 1) : d321199 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34108, d321199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34108, d321199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34111 q = 1) (hb : d318725 q = 1) : d321202 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34111, d321202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85740 q ha hb
    | true =>
      simp only [d34111, d321202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85710 q ha hb
  have h9 (q : Pattern) (ha : d34112 q = 1) (hb : d318725 q = 1) : d321203 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34112, d321203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34112, d321203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34113 q = 1) (hb : d318725 q = 1) : d321204 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34113, d321204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34113, d321204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34115 q = 1) (hb : d318725 q = 1) : d321206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85710 q ha hb
    | true =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85711 q ha hb
  have h12 (q : Pattern) (ha : d34116 q = 1) (hb : d318725 q = 1) : d321207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d34117 q = 1) (hb : d318725 q = 1) : d321208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34118 q = 1) (hb : d318725 q = 1) : d321209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34118, d321209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34118, d321209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d34119 q = 1) (hb : d318725 q = 1) : d321210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34119, d321210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34119, d321210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d34120 q = 1) (hb : d318725 q = 1) : d321211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34120, d321211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d34120, d321211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro85743 (p : Pattern) (ha : d34125 p = 1) (hb : d318725 p = 1) : d321216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34111 q = 1) (hb : d318725 q = 1) : d321202 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34111, d321202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85740 q ha hb
    | true =>
      simp only [d34111, d321202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85710 q ha hb
  have h2 (q : Pattern) (ha : d34112 q = 1) (hb : d318725 q = 1) : d321203 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34112, d321203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34112, d321203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34113 q = 1) (hb : d318725 q = 1) : d321204 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34113, d321204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34113, d321204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34115 q = 1) (hb : d318725 q = 1) : d321206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85710 q ha hb
    | true =>
      simp only [d34115, d321206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85711 q ha hb
  have h5 (q : Pattern) (ha : d34116 q = 1) (hb : d318725 q = 1) : d321207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d321207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34117 q = 1) (hb : d318725 q = 1) : d321208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d321208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34118 q = 1) (hb : d318725 q = 1) : d321209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34118, d321209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34118, d321209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34123 q = 1) (hb : d318725 q = 1) : d321214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34123, d321214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34123, d321214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34124 q = 1) (hb : d318725 q = 1) : d321215 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34124, d321215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34124, d321215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34125 q = 1) (hb : d318725 q = 1) : d321216 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34125, d321216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34125, d321216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro85744 (p : Pattern) (ha : d34131 p = 1) (hb : d318725 p = 1) : d321222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34121 q = 1) (hb : d318725 q = 1) : d321212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34121, d321212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85742 q ha hb
    | true =>
      simp only [d34121, d321212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34122 q = 1) (hb : d318725 q = 1) : d321213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34122, d321213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34122, d321213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34126 q = 1) (hb : d318725 q = 1) : d321217 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85743 q ha hb
    | true =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34127 q = 1) (hb : d318725 q = 1) : d321218 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34128 q = 1) (hb : d318725 q = 1) : d321219 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34128, d321219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34128, d321219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34129 q = 1) (hb : d318725 q = 1) : d321220 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34129, d321220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34129, d321220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34130 q = 1) (hb : d318725 q = 1) : d321221 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34130, d321221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34130, d321221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34131 q = 1) (hb : d318725 q = 1) : d321222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34131, d321222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34131, d321222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85745 (p : Pattern) (ha : d34139 p = 1) (hb : d318725 p = 1) : d321230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34126 q = 1) (hb : d318725 q = 1) : d321217 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85743 q ha hb
    | true =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34127 q = 1) (hb : d318725 q = 1) : d321218 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34134 q = 1) (hb : d318725 q = 1) : d321225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34134, d321225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85712 q ha hb
    | true =>
      simp only [d34134, d321225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34135 q = 1) (hb : d318725 q = 1) : d321226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34135, d321226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34135, d321226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34136 q = 1) (hb : d318725 q = 1) : d321227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34136, d321227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34136, d321227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34137 q = 1) (hb : d318725 q = 1) : d321228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34137, d321228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34137, d321228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34138 q = 1) (hb : d318725 q = 1) : d321229 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34138, d321229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34138, d321229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34139 q = 1) (hb : d318725 q = 1) : d321230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34139, d321230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34139, d321230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro85746 (p : Pattern) (ha : d34193 p = 1) (hb : d318725 p = 1) : d321236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34126 q = 1) (hb : d318725 q = 1) : d321217 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85743 q ha hb
    | true =>
      simp only [d34126, d321217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34127 q = 1) (hb : d318725 q = 1) : d321218 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d321218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34190 q = 1) (hb : d318725 q = 1) : d321233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34190, d321233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34190, d321233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34191 q = 1) (hb : d318725 q = 1) : d321234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34191, d321234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34191, d321234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34192 q = 1) (hb : d318725 q = 1) : d321235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34192, d321235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34192, d321235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34193 q = 1) (hb : d318725 q = 1) : d321236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34193, d321236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34193, d321236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro85747 (p : Pattern) (ha : d266054 p = 1) (hb : d318725 p = 1) : d321242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34140 q = 1) (hb : d318725 q = 1) : d321231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34140, d321231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85744 q ha hb
    | true =>
      simp only [d34140, d321231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85745 q ha hb
  have h2 (q : Pattern) (ha : d266050 q = 1) (hb : d318725 q = 1) : d321232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d321232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266050, d321232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34194 q = 1) (hb : d318725 q = 1) : d321237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34194, d321237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85746 q ha hb
    | true =>
      simp only [d34194, d321237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34195 q = 1) (hb : d318725 q = 1) : d321238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34195, d321238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34195, d321238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d318725 q = 1) : d321239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d321239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266051, d321239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d318725 q = 1) : d321240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d321240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d321240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d318725 q = 1) : d321241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d321241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d321241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d318725 q = 1) : d321242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d321242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d321242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro85748 (p : Pattern) (ha : d266060 p = 1) (hb : d318725 p = 1) : d321259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33863 q = 1) (hb : d318725 q = 1) : d321029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33863, d321029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33863, d321029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85703 q ha hb
  have h2 (q : Pattern) (ha : d33864 q = 1) (hb : d318725 q = 1) : d321030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33864, d321030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33864, d321030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33873 q = 1) (hb : d318725 q = 1) : d321039 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33873, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85703 q ha hb
    | true =>
      simp only [d33873, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85706 q ha hb
  have h4 (q : Pattern) (ha : d33874 q = 1) (hb : d318725 q = 1) : d321040 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33874, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33874, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33875 q = 1) (hb : d318725 q = 1) : d321041 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33875, d321041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33875, d321041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266038 q = 1) (hb : d318725 q = 1) : d321143 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d321143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85730 q ha hb
    | true =>
      simp only [d266038, d321143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85737 q ha hb
  have h7 (q : Pattern) (ha : d34065 q = 1) (hb : d318725 q = 1) : d321156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34065, d321156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85707 q ha hb
    | true =>
      simp only [d34065, d321156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85708 q ha hb
  have h8 (q : Pattern) (ha : d266039 q = 1) (hb : d318725 q = 1) : d321157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d321157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266039, d321157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266040 q = 1) (hb : d318725 q = 1) : d321158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d321158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266040, d321158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d266041 q = 1) (hb : d318725 q = 1) : d321159 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d321159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266041, d321159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266045 q = 1) (hb : d318725 q = 1) : d321163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d321163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266045, d321163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85738 q ha hb
  have h12 (q : Pattern) (ha : d34074 q = 1) (hb : d318725 q = 1) : d321165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34074, d321165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34074, d321165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85709 q ha hb
  have h13 (q : Pattern) (ha : d266046 q = 1) (hb : d318725 q = 1) : d321166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d321166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d266046, d321166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266047 q = 1) (hb : d318725 q = 1) : d321167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d321167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266047, d321167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d266048 q = 1) (hb : d318725 q = 1) : d321168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d321168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266048, d321168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d266049 q = 1) (hb : d318725 q = 1) : d321169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d321169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266049, d321169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266055 q = 1) (hb : d318725 q = 1) : d321243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d321243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266055, d321243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85747 q ha hb
  have h18 (q : Pattern) (ha : d34211 q = 1) (hb : d318725 q = 1) : d321254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34211, d321254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34211, d321254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85714 q ha hb
  have h19 (q : Pattern) (ha : d266056 q = 1) (hb : d318725 q = 1) : d321255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d321255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266056, d321255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d266057 q = 1) (hb : d318725 q = 1) : d321256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d321256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d266057, d321256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d266058 q = 1) (hb : d318725 q = 1) : d321257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d321257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d266058, d321257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d266059 q = 1) (hb : d318725 q = 1) : d321258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d321258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266059, d321258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d266060 q = 1) (hb : d318725 q = 1) : d321259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d321259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266060, d321259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro85749 (p : Pattern) (ha : d266066 p = 1) (hb : d318725 p = 1) : d321265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d318725 q = 1) : d321260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d321260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d321260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85748 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d318725 q = 1) : d321261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d321261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d321261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d318725 q = 1) : d321262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d321262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d321262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d318725 q = 1) : d321263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d321263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d321263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d318725 q = 1) : d321264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d321264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d321264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d318725 q = 1) : d321265 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d321265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d321265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
