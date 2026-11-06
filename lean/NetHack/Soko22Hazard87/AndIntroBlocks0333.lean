import NetHack.Soko22Hazard87.AndIntroBlocks0332
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro83250 (p : Pattern) (ha : d261985 p = 1) (hb : d312503 p = 1) : d300013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34898 q = 1) (hb : d261985 q = 1) : d299268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34898, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82767 q ha hb
    | true =>
      simp only [d34898, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82770 q ha hb
  have h2 (q : Pattern) (ha : d34899 q = 1) (hb : d261985 q = 1) : d299269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34899, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34899, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312484 q = 1) : d299994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312484, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312484, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312485 q = 1) : d299995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312485, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312485, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312487 q = 1) : d299997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312487, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312487, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83248 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312488 q = 1) : d299998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312488, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312488, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d312489 q = 1) : d299999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312489, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312489, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d312490 q = 1) : d300000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312490, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312490, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d312491 q = 1) : d300001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312491, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312491, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d312498 q = 1) : d300008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312498, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312498, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83249 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d312499 q = 1) : d300009 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312499, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312499, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d312500 q = 1) : d300010 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312500, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312500, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d312501 q = 1) : d300011 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312501, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312501, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d312502 q = 1) : d300012 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312502, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312502, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d312503 q = 1) : d300013 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312503, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312503, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83251 (p : Pattern) (ha : d261985 p = 1) (hb : d312509 p = 1) : d300019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312504 q = 1) : d300014 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312504, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312504, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83250 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312505 q = 1) : d300015 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312505, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312505, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312506 q = 1) : d300016 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312506, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312506, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312507 q = 1) : d300017 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312507, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312507, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312508 q = 1) : d300018 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312508, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312508, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312509 q = 1) : d300019 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312509, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312509, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83252 (p : Pattern) (ha : d261985 p = 1) (hb : d312516 p = 1) : d300026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35475 q = 1) (hb : d261985 q = 1) : d299600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d35475, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82837 q ha hb
    | true =>
      simp only [d35475, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82838 q ha hb
  have h2 (q : Pattern) (ha : d35476 q = 1) (hb : d261985 q = 1) : d299601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d35476, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35476, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35477 q = 1) (hb : d261985 q = 1) : d299602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d35477, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35477, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35478 q = 1) (hb : d261985 q = 1) : d299603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d35478, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35478, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35479 q = 1) (hb : d261985 q = 1) : d299604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d35479, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35479, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312516 q = 1) : d300026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312516, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312516, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83253 (p : Pattern) (ha : d261985 p = 1) (hb : d312523 p = 1) : d299767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35771 q = 1) (hb : d261985 q = 1) : d299752 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35771, d299752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82873 q ha hb
    | true =>
      simp only [d35771, d299752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82845 q ha hb
  have h2 (q : Pattern) (ha : d35772 q = 1) (hb : d261985 q = 1) : d299753 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35772, d299753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35772, d299753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35773 q = 1) (hb : d261985 q = 1) : d299754 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35773, d299754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35773, d299754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35780 q = 1) (hb : d261985 q = 1) : d299757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35780, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82845 q ha hb
    | true =>
      simp only [d35780, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82875 q ha hb
  have h5 (q : Pattern) (ha : d35781 q = 1) (hb : d261985 q = 1) : d299758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35781, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35781, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35782 q = 1) (hb : d261985 q = 1) : d299759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35782, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35782, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d35783 q = 1) (hb : d261985 q = 1) : d299760 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35783, d299760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35783, d299760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d35799 q = 1) (hb : d261985 q = 1) : d299757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35799, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82845 q ha hb
    | true =>
      simp only [d35799, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82846 q ha hb
  have h9 (q : Pattern) (ha : d35800 q = 1) (hb : d261985 q = 1) : d299758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35800, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35800, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d35801 q = 1) (hb : d261985 q = 1) : d299759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35801, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35801, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d35802 q = 1) (hb : d261985 q = 1) : d299765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35802, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d35802, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d312522 q = 1) : d299766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312522, d299766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312522, d299766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d312523 q = 1) : d299767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312523, d299767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312523, d299767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro83254 (p : Pattern) (ha : d261985 p = 1) (hb : d312529 p = 1) : d299781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312524 q = 1) : d299768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312524, d299768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83253 q ha hb
    | true =>
      simp only [d312524, d299768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312525 q = 1) : d299769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312525, d299769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312525, d299769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35805 q = 1) (hb : d261985 q = 1) : d299776 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d35805, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82847 q ha hb
    | true =>
      simp only [d35805, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35806 q = 1) (hb : d261985 q = 1) : d299777 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d35806, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35806, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312526 q = 1) : d299778 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312526, d299778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312526, d299778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312527 q = 1) : d299779 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312527, d299779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312527, d299779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d312528 q = 1) : d299780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312528, d299780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312528, d299780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d312529 q = 1) : d299781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312529, d299781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312529, d299781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83255 (p : Pattern) (ha : d258695 p = 1) (hb : d261985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261984 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d258695 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d258695, d261985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258695, d261985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro83256 (p : Pattern) (ha : d261985 p = 1) (hb : d312535 p = 1) : d10411 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312532 q = 1) : d2076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d312532, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312532, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10408 q = 1) (hb : d261985 q = 1) : d10408 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d312533 q = 1) : d10409 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d312533, d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312533, d10409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d312534 q = 1) : d10410 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d312534, d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312534, d10410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d312535 q = 1) : d10411 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d312535, d10411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d312535, d10411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h9 p ha hb
theorem andIntro83257 (p : Pattern) (ha : d261985 p = 1) (hb : d312541 p = 1) : d299756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35765 q = 1) (hb : d261985 q = 1) : d299746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35765, d299746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35765, d299746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82827 q ha hb
  have h2 (q : Pattern) (ha : d35417 q = 1) (hb : d261985 q = 1) : d299557 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35417, d299557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82827 q ha hb
    | true =>
      simp only [d35417, d299557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35766 q = 1) (hb : d261985 q = 1) : d299747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35766, d299747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35766, d299747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35418 q = 1) (hb : d261985 q = 1) : d299558 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35418, d299558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35418, d299558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35767 q = 1) (hb : d261985 q = 1) : d299748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35767, d299748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35767, d299748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35768 q = 1) (hb : d261985 q = 1) : d299749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35768, d299749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35768, d299749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35797 q = 1) (hb : d261985 q = 1) : d299755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d35797, d299755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35797, d299755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15791 q = 1) (hb : d261985 q = 1) : d15791 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d312536 q = 1) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d312536, d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83256 q ha hb
    | true =>
      simp only [d312536, d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d312537 q = 1) : d10414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d312537, d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312537, d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d312538 q = 1) : d15792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d312538, d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d312538, d15792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d312539 q = 1) : d15793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d312539, d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312539, d15793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d312540 q = 1) : d15794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d312540, d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312540, d15794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d312541 q = 1) : d299756 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d312541, d299756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312541, d299756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro83258 (p : Pattern) (ha : d261985 p = 1) (hb : d312547 p = 1) : d299775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312542 q = 1) : d299757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d312542, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82845 q hb ha
    | true =>
      simp only [d312542, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83257 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312543 q = 1) : d299758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d312543, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312543, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312544 q = 1) : d299759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d312544, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312544, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312545 q = 1) : d299765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d312545, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312545, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312546 q = 1) : d299774 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312546, d299774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312546, d299774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312547 q = 1) : d299775 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312547, d299775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312547, d299775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83259 (p : Pattern) (ha : d261985 p = 1) (hb : d312553 p = 1) : d299818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312548 q = 1) : d299776 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312548, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83258 q ha hb
    | true =>
      simp only [d312548, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312549 q = 1) : d299777 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312549, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312549, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312550 q = 1) : d299815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312550, d299815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312550, d299815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312551 q = 1) : d299816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312551, d299816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312551, d299816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312552 q = 1) : d299817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312552, d299817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312552, d299817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312553 q = 1) : d299818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312553, d299818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312553, d299818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83260 (p : Pattern) (ha : d261985 p = 1) (hb : d312559 p = 1) : d300037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312554 q = 1) : d300032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312554, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83254 q ha hb
    | true =>
      simp only [d312554, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83259 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312555 q = 1) : d300033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312555, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312555, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312556 q = 1) : d300034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312556, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312556, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312557 q = 1) : d300035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312557, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312557, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312558 q = 1) : d300036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312558, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312558, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312559 q = 1) : d300037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312559, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312559, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83261 (p : Pattern) (ha : d261985 p = 1) (hb : d312565 p = 1) : d300043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35481 q = 1) (hb : d261985 q = 1) : d299606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d35481, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82836 q ha hb
    | true =>
      simp only [d35481, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82839 q ha hb
  have h2 (q : Pattern) (ha : d35482 q = 1) (hb : d261985 q = 1) : d299607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d35482, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35482, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312514 q = 1) : d300024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312514, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312514, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312515 q = 1) : d300025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312515, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312515, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312517 q = 1) : d300027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312517, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312517, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83252 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312518 q = 1) : d300028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312518, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312518, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d312519 q = 1) : d300029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312519, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312519, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d312520 q = 1) : d300030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312520, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312520, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d312521 q = 1) : d300031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312521, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312521, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d312560 q = 1) : d300038 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312560, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312560, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83260 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d312561 q = 1) : d300039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312561, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312561, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d312562 q = 1) : d300040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312562, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312562, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d312563 q = 1) : d300041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312563, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312563, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d312564 q = 1) : d300042 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312564, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312564, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d312565 q = 1) : d300043 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312565, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312565, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83262 (p : Pattern) (ha : d261985 p = 1) (hb : d312571 p = 1) : d300049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312566 q = 1) : d300044 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312566, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312566, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83261 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312567 q = 1) : d300045 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312567, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312567, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312568 q = 1) : d300046 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312568, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312568, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312569 q = 1) : d300047 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312569, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312569, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312570 q = 1) : d300048 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312570, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312570, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312571 q = 1) : d300049 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312571, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312571, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83263 (p : Pattern) (ha : d261985 p = 1) (hb : d312577 p = 1) : d300055 p = 1 := by
  have h0 (q : Pattern) (ha : d261985 q = 1) (hb : d312426 q = 1) : d299936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312426, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83235 q ha hb
    | true =>
      simp only [d312426, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83239 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312453 q = 1) : d299963 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312453, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312453, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83243 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312454 q = 1) : d299964 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312454, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312454, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312481 q = 1) : d299991 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312481, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312481, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83247 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312482 q = 1) : d299992 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312482, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312482, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312483 q = 1) : d299993 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312483, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312483, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d312510 q = 1) : d300020 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312510, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312510, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83251 q ha hb
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d312511 q = 1) : d300021 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312511, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312511, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d312512 q = 1) : d300022 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312512, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312512, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d312513 q = 1) : d300023 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312513, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312513, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d312572 q = 1) : d300050 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312572, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312572, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83262 q ha hb
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d312573 q = 1) : d300051 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312573, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312573, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d312574 q = 1) : d300052 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312574, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312574, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d312575 q = 1) : d300053 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312575, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312575, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d312576 q = 1) : d300054 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d312576, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312576, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d261985 q = 1) (hb : d312577 q = 1) : d300055 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d312577, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312577, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro83264 (p : Pattern) (ha : d261985 p = 1) (hb : d312583 p = 1) : d300061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312578 q = 1) : d300056 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d312578, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83263 q ha hb
    | true =>
      simp only [d312578, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312579 q = 1) : d300057 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d312579, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312579, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312580 q = 1) : d300058 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d312580, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312580, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312581 q = 1) : d300059 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d312581, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312581, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312582 q = 1) : d300060 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d312582, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312582, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312583 q = 1) : d300061 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d312583, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312583, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83265 (p : Pattern) (ha : d261985 p = 1) (hb : d312589 p = 1) : d300067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312584 q = 1) : d300062 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d312584, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83264 q ha hb
    | true =>
      simp only [d312584, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312585 q = 1) : d300063 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d312585, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312585, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312586 q = 1) : d300064 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d312586, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312586, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312587 q = 1) : d300065 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d312587, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312587, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312588 q = 1) : d300066 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d312588, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312588, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312589 q = 1) : d300067 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d312589, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312589, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83266 (p : Pattern) (ha : d261985 p = 1) (hb : d312595 p = 1) : d300073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312590 q = 1) : d300068 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d312590, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83265 q ha hb
    | true =>
      simp only [d312590, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312591 q = 1) : d300069 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d312591, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312591, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312592 q = 1) : d300070 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d312592, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312592, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312593 q = 1) : d300071 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d312593, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312593, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312594 q = 1) : d300072 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d312594, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312594, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312595 q = 1) : d300073 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d312595, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312595, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83267 (p : Pattern) (ha : d261985 p = 1) (hb : d312601 p = 1) : d300079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312596 q = 1) : d300074 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d312596, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83266 q ha hb
    | true =>
      simp only [d312596, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312597 q = 1) : d300075 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d312597, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312597, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312598 q = 1) : d300076 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d312598, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312598, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312599 q = 1) : d300077 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d312599, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312599, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312600 q = 1) : d300078 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d312600, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312600, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312601 q = 1) : d300079 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d312601, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312601, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83268 (p : Pattern) (ha : d261985 p = 1) (hb : d312607 p = 1) : d300085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312602 q = 1) : d300080 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d312602, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83267 q ha hb
    | true =>
      simp only [d312602, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312603 q = 1) : d300081 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d312603, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312603, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312604 q = 1) : d300082 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d312604, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312604, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312605 q = 1) : d300083 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d312605, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312605, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312606 q = 1) : d300084 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d312606, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312606, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312607 q = 1) : d300085 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d312607, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312607, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83269 (p : Pattern) (ha : d261985 p = 1) (hb : d312613 p = 1) : d300091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312608 q = 1) : d300086 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d312608, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83268 q ha hb
    | true =>
      simp only [d312608, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312609 q = 1) : d300087 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d312609, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312609, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312610 q = 1) : d300088 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d312610, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312610, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312611 q = 1) : d300089 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d312611, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312611, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312612 q = 1) : d300090 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d312612, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312612, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312613 q = 1) : d300091 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d312613, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312613, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83270 (p : Pattern) (ha : d261985 p = 1) (hb : d312619 p = 1) : d300097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d312614 q = 1) : d300092 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d312614, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83269 q ha hb
    | true =>
      simp only [d312614, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d312615 q = 1) : d300093 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d312615, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312615, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d312616 q = 1) : d300094 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d312616, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312616, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d312617 q = 1) : d300095 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d312617, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312617, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d312618 q = 1) : d300096 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d312618, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312618, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d312619 q = 1) : d300097 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d312619, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312619, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83271 (p : Pattern) (ha : d241986 p = 1) (hb : d298159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d241855 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82899 q ha hb
    | true =>
      simp only [d241855, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d241976 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d241976, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241983 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241983, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241984 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241984, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241985 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241985, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241986 q = 1) (hb : d298159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d241986, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241986, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83272 (p : Pattern) (ha : d242005 p = 1) (hb : d298166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d241855 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82899 q ha hb
    | true =>
      simp only [d241855, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d241976 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241976, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d241983 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241983, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d241984 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241984, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241985 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241985, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d241862 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82901 q ha hb
    | true =>
      simp only [d241862, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d241998 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d241998, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242002 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242002, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242003 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242003, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242003, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242004 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242004, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242004, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242005 q = 1) (hb : d298166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242005, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242005, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83273 (p : Pattern) (ha : d242014 p = 1) (hb : d299887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241862 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82901 q ha hb
    | true =>
      simp only [d241862, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d241998 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241998, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242002 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242002, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242012 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242012, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242012, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242013 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242013, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242013, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242014 q = 1) (hb : d299887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242014, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242014, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83274 (p : Pattern) (ha : d242054 p = 1) (hb : d299897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241898 q = 1) (hb : d298138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241898, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82906 q ha hb
    | true =>
      simp only [d241898, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d242044 q = 1) (hb : d299893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242044, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242044, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242051 q = 1) (hb : d299894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242051, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242051, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242052 q = 1) (hb : d299895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242052, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242052, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242053 q = 1) (hb : d299896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242053, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242053, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242054 q = 1) (hb : d299897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242054, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242054, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83275 (p : Pattern) (ha : d242060 p = 1) (hb : d299903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242006 q = 1) (hb : d298167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242006, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83271 q ha hb
    | true =>
      simp only [d242006, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83272 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242009 q = 1) (hb : d298168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242009, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242009, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242010 q = 1) (hb : d299885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242010, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242010, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242011 q = 1) (hb : d299886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242011, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242011, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242015 q = 1) (hb : d299888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242015, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242015, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83273 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242016 q = 1) (hb : d299889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242016, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242016, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242017 q = 1) (hb : d299890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242017, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242017, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242018 q = 1) (hb : d299891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242018, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242018, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242019 q = 1) (hb : d299892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242019, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242019, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242055 q = 1) (hb : d299898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242055, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242055, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83274 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242056 q = 1) (hb : d299899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242056, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242056, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242057 q = 1) (hb : d299900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242057, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242057, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242058 q = 1) (hb : d299901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242058, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242058, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242059 q = 1) (hb : d299902 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242059, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242059, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242060 q = 1) (hb : d299903 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242060, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242060, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83276 (p : Pattern) (ha : d242066 p = 1) (hb : d299909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d241910 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61294 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d241911 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d241912 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d241913 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d241914 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242061 q = 1) (hb : d299904 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242061, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242061, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83275 q ha hb
  have h8 (q : Pattern) (ha : d242062 q = 1) (hb : d299905 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242062, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242062, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242063 q = 1) (hb : d299906 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242063, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242063, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242064 q = 1) (hb : d299907 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242064, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242064, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d242065 q = 1) (hb : d299908 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242065, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242065, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d242066 q = 1) (hb : d299909 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242066, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d242066, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro83277 (p : Pattern) (ha : d242177 p = 1) (hb : d298326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242084 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82937 q ha hb
    | true =>
      simp only [d242084, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82938 q ha hb
  have h5 (q : Pattern) (ha : d242167 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242167, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242174 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242174, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242175 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242175, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242176 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242176, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242177 q = 1) (hb : d298326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242177, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242177, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83278 (p : Pattern) (ha : d242198 p = 1) (hb : d298336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242084 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82937 q ha hb
    | true =>
      simp only [d242084, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82938 q ha hb
  have h4 (q : Pattern) (ha : d242167 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242167, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242174 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242174, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242175 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242175, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242176 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242176, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242094 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82940 q ha hb
    | true =>
      simp only [d242094, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82941 q ha hb
  have h13 (q : Pattern) (ha : d242191 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242191, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242195 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242195, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242196 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242196, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242196, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242197 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242197, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242197, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242198 q = 1) (hb : d298336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242198, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242198, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83279 (p : Pattern) (ha : d242218 p = 1) (hb : d299912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242094 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82940 q ha hb
    | true =>
      simp only [d242094, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82941 q ha hb
  have h3 (q : Pattern) (ha : d242191 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242191, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242195 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242195, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242216 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242216, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242216, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242217 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242217, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242217, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242218 q = 1) (hb : d299912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242218, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242218, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83280 (p : Pattern) (ha : d242286 p = 1) (hb : d299923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242275 q = 1) (hb : d299918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242275, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82975 q ha hb
    | true =>
      simp only [d242275, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82978 q ha hb
  have h3 (q : Pattern) (ha : d242276 q = 1) (hb : d299919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242276, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242276, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242282 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242283 q = 1) (hb : d299920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242283, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242283, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242284 q = 1) (hb : d299921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242284, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242284, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242285 q = 1) (hb : d299922 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242285, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242285, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242286 q = 1) (hb : d299923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242286, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242286, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83281 (p : Pattern) (ha : d242299 p = 1) (hb : d299929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242199 q = 1) (hb : d298337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242199, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83277 q ha hb
    | true =>
      simp only [d242199, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83278 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242213 q = 1) (hb : d298338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242213, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242213, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242214 q = 1) (hb : d299910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242214, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242214, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242215 q = 1) (hb : d299911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242215, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242215, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242219 q = 1) (hb : d299913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242219, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242219, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83279 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242221 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242222 q = 1) (hb : d299914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242222, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242222, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242223 q = 1) (hb : d299915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242223, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242223, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242224 q = 1) (hb : d299916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242224, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242224, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242225 q = 1) (hb : d299917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242225, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242225, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242287 q = 1) (hb : d299924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242287, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242287, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83280 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242294 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242295 q = 1) (hb : d299925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242295, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242295, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242296 q = 1) (hb : d299926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242296, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242296, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242297 q = 1) (hb : d299927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242297, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242297, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242298 q = 1) (hb : d299928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242298, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242298, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242299 q = 1) (hb : d299929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242299, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242299, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83282 (p : Pattern) (ha : d242305 p = 1) (hb : d299935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242300 q = 1) (hb : d299930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242300, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242300, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83281 q ha hb
  have h2 (q : Pattern) (ha : d242301 q = 1) (hb : d299931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242301, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242301, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242302 q = 1) (hb : d299932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242302, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242302, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242303 q = 1) (hb : d299933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242303, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242303, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242304 q = 1) (hb : d299934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242304, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242304, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242305 q = 1) (hb : d299935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242305, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242305, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83283 (p : Pattern) (ha : d242435 p = 1) (hb : d298576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242342 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82988 q ha hb
    | true =>
      simp only [d242342, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82989 q ha hb
  have h5 (q : Pattern) (ha : d242425 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242425, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242432 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242432, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242433 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242433, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242434 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242434, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242435 q = 1) (hb : d298576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242435, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242435, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83284 (p : Pattern) (ha : d242456 p = 1) (hb : d298586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242342 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82988 q ha hb
    | true =>
      simp only [d242342, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82989 q ha hb
  have h4 (q : Pattern) (ha : d242425 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242425, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242432 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242432, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242433 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242433, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242434 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242434, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242352 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82991 q ha hb
    | true =>
      simp only [d242352, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82992 q ha hb
  have h13 (q : Pattern) (ha : d242449 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242449, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242453 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242453, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242454 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242454, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242454, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242455 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242455, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242455, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242456 q = 1) (hb : d298586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242456, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242456, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83285 (p : Pattern) (ha : d242476 p = 1) (hb : d299939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242352 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82991 q ha hb
    | true =>
      simp only [d242352, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82992 q ha hb
  have h3 (q : Pattern) (ha : d242449 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242449, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242453 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242453, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242474 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242474, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242474, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242475 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242475, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242475, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242476 q = 1) (hb : d299939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242476, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242476, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83286 (p : Pattern) (ha : d242561 p = 1) (hb : d299950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242550 q = 1) (hb : d299945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242550, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83029 q ha hb
    | true =>
      simp only [d242550, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83032 q ha hb
  have h3 (q : Pattern) (ha : d242551 q = 1) (hb : d299946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242551, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242551, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242558 q = 1) (hb : d299947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242558, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242558, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242559 q = 1) (hb : d299948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242559, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242559, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242560 q = 1) (hb : d299949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242560, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242560, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242561 q = 1) (hb : d299950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242561, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242561, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83287 (p : Pattern) (ha : d242574 p = 1) (hb : d299956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242457 q = 1) (hb : d298587 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242457, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83283 q ha hb
    | true =>
      simp only [d242457, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83284 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242471 q = 1) (hb : d298588 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242471, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242471, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242472 q = 1) (hb : d299937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242472, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242472, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242473 q = 1) (hb : d299938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242473, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242473, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242477 q = 1) (hb : d299940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242477, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242477, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83285 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242479 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242480 q = 1) (hb : d299941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242480, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242480, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242481 q = 1) (hb : d299942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242481, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242481, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242482 q = 1) (hb : d299943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242482, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242482, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242483 q = 1) (hb : d299944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242483, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242483, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242562 q = 1) (hb : d299951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242562, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242562, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83286 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242570 q = 1) (hb : d299952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242570, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242570, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242571 q = 1) (hb : d299953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242571, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242571, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242572 q = 1) (hb : d299954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242572, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242572, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242573 q = 1) (hb : d299955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242573, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242573, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242574 q = 1) (hb : d299956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242574, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242574, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83288 (p : Pattern) (ha : d242580 p = 1) (hb : d299962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242575 q = 1) (hb : d299957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242575, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242575, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83287 q ha hb
  have h2 (q : Pattern) (ha : d242576 q = 1) (hb : d299958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242576, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242576, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242577 q = 1) (hb : d299959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242577, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242577, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242578 q = 1) (hb : d299960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242578, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242578, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242579 q = 1) (hb : d299961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242579, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242579, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242580 q = 1) (hb : d299962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242580, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242580, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83289 (p : Pattern) (ha : d242768 p = 1) (hb : d298890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242662 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83047 q ha hb
    | true =>
      simp only [d242662, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83048 q ha hb
  have h5 (q : Pattern) (ha : d242749 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242749, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242765 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242765, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242766 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242766, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242767 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242767, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242768 q = 1) (hb : d298890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242768, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242768, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83290 (p : Pattern) (ha : d242789 p = 1) (hb : d298900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242662 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83047 q ha hb
    | true =>
      simp only [d242662, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83048 q ha hb
  have h4 (q : Pattern) (ha : d242749 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242749, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242765 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242765, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242766 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242766, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242767 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242767, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242672 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83050 q ha hb
    | true =>
      simp only [d242672, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83051 q ha hb
  have h13 (q : Pattern) (ha : d242782 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242782, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242786 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242786, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242787 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242787, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242787, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242788 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242788, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242788, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242789 q = 1) (hb : d298900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242789, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242789, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83291 (p : Pattern) (ha : d242809 p = 1) (hb : d299967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242672 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83050 q ha hb
    | true =>
      simp only [d242672, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83051 q ha hb
  have h3 (q : Pattern) (ha : d242782 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242782, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242786 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242786, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242807 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242807, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242807, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242808 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242808, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242808, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242809 q = 1) (hb : d299967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242809, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242809, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83292 (p : Pattern) (ha : d242930 p = 1) (hb : d299978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242910 q = 1) (hb : d299973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242910, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83089 q ha hb
    | true =>
      simp only [d242910, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83094 q ha hb
  have h3 (q : Pattern) (ha : d242911 q = 1) (hb : d299974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242911, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242911, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242927 q = 1) (hb : d299975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242927, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242927, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242928 q = 1) (hb : d299976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242928, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242928, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242929 q = 1) (hb : d299977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242929, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242929, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242930 q = 1) (hb : d299978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242930, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242930, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83293 (p : Pattern) (ha : d242943 p = 1) (hb : d299984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242790 q = 1) (hb : d298901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242790, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83289 q ha hb
    | true =>
      simp only [d242790, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83290 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242804 q = 1) (hb : d298902 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242804, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242804, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242805 q = 1) (hb : d299965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242805, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242805, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242806 q = 1) (hb : d299966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242806, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242806, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242810 q = 1) (hb : d299968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242810, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242810, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83291 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242812 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242813 q = 1) (hb : d299969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242813, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242813, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242814 q = 1) (hb : d299970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242814, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242814, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242815 q = 1) (hb : d299971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242815, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242815, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242816 q = 1) (hb : d299972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242816, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242816, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242931 q = 1) (hb : d299979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242931, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242931, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83292 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242938 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242939 q = 1) (hb : d299980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242939, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242939, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242940 q = 1) (hb : d299981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242940, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242940, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242941 q = 1) (hb : d299982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242941, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242941, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242942 q = 1) (hb : d299983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242942, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242942, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242943 q = 1) (hb : d299984 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242943, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242943, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83294 (p : Pattern) (ha : d242949 p = 1) (hb : d299990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242944 q = 1) (hb : d299985 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242944, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242944, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83293 q ha hb
  have h2 (q : Pattern) (ha : d242945 q = 1) (hb : d299986 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242945, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242945, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242946 q = 1) (hb : d299987 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242946, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242946, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242947 q = 1) (hb : d299988 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242947, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242947, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242948 q = 1) (hb : d299989 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242948, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242948, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242949 q = 1) (hb : d299990 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242949, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242949, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83295 (p : Pattern) (ha : d243151 p = 1) (hb : d299257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243045 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83110 q ha hb
    | true =>
      simp only [d243045, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83111 q ha hb
  have h5 (q : Pattern) (ha : d243119 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243119, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243148 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243148, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243149 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243149, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243150 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243150, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243151 q = 1) (hb : d299257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83296 (p : Pattern) (ha : d243172 p = 1) (hb : d299267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243045 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83110 q ha hb
    | true =>
      simp only [d243045, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83111 q ha hb
  have h4 (q : Pattern) (ha : d243119 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243119, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243148 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243148, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243149 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243149, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243150 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243150, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243162 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243055 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83113 q ha hb
    | true =>
      simp only [d243055, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83114 q ha hb
  have h13 (q : Pattern) (ha : d243165 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243165, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243169 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243169, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243170 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243170, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243171 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243171, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243172 q = 1) (hb : d299267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243172, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83297 (p : Pattern) (ha : d243192 p = 1) (hb : d299996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243055 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83113 q ha hb
    | true =>
      simp only [d243055, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83114 q ha hb
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243165, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243169 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243190 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243191 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243192 q = 1) (hb : d299996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83298 (p : Pattern) (ha : d243320 p = 1) (hb : d300007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243289 q = 1) (hb : d300002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243289, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83153 q ha hb
    | true =>
      simp only [d243289, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83159 q ha hb
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d300003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243290, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243317 q = 1) (hb : d300004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243318 q = 1) (hb : d300005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243319 q = 1) (hb : d300006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243320 q = 1) (hb : d300007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83299 (p : Pattern) (ha : d243333 p = 1) (hb : d300013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243173 q = 1) (hb : d299268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83295 q ha hb
    | true =>
      simp only [d243173, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83296 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243187 q = 1) (hb : d299269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243187, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243188 q = 1) (hb : d299994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243188, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243189 q = 1) (hb : d299995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243189, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243193 q = 1) (hb : d299997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243193, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83297 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243196 q = 1) (hb : d299998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243196, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243197 q = 1) (hb : d299999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243197, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243198 q = 1) (hb : d300000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243198, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243199 q = 1) (hb : d300001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243199, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243321 q = 1) (hb : d300008 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243321, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83298 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243329 q = 1) (hb : d300009 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243329, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243330 q = 1) (hb : d300010 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243330, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243331 q = 1) (hb : d300011 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243331, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243332 q = 1) (hb : d300012 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243332, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243333 q = 1) (hb : d300013 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243333, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83300 (p : Pattern) (ha : d243339 p = 1) (hb : d300019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d300014 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83299 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d300015 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d300016 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d300017 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d300018 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d300019 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83301 (p : Pattern) (ha : d243516 p = 1) (hb : d299595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243423 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83173 q ha hb
    | true =>
      simp only [d243423, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83174 q ha hb
  have h5 (q : Pattern) (ha : d243478 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243478, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243513 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243513, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243514 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243514, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243515 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243515, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243516 q = 1) (hb : d299595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243516, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243516, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83302 (p : Pattern) (ha : d243537 p = 1) (hb : d299605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243423 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83173 q ha hb
    | true =>
      simp only [d243423, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83174 q ha hb
  have h4 (q : Pattern) (ha : d243478 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243478, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243513 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243513, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243514 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243514, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243515 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243515, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243433 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83176 q ha hb
    | true =>
      simp only [d243433, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83177 q ha hb
  have h13 (q : Pattern) (ha : d243530 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243530, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243534 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243534, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243535 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243535, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243535, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243536 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243536, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243536, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243537 q = 1) (hb : d299605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243537, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243537, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83303 (p : Pattern) (ha : d243557 p = 1) (hb : d300026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243433 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83176 q ha hb
    | true =>
      simp only [d243433, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83177 q ha hb
  have h3 (q : Pattern) (ha : d243530 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243530, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243534 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243534, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243555 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243555, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243555, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243556 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243556, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243556, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243557 q = 1) (hb : d300026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83304 (p : Pattern) (ha : d243667 p = 1) (hb : d300037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243636 q = 1) (hb : d300032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243636, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83214 q ha hb
    | true =>
      simp only [d243636, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83220 q ha hb
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d300033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243664 q = 1) (hb : d300034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243665 q = 1) (hb : d300035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243666 q = 1) (hb : d300036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243667 q = 1) (hb : d300037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83305 (p : Pattern) (ha : d243680 p = 1) (hb : d300043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243538 q = 1) (hb : d299606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83301 q ha hb
    | true =>
      simp only [d243538, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83302 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243552 q = 1) (hb : d299607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243552, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243553 q = 1) (hb : d300024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243553, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243554 q = 1) (hb : d300025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243554, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243558 q = 1) (hb : d300027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243558, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83303 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243561 q = 1) (hb : d300028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243561, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243562 q = 1) (hb : d300029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243562, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243563 q = 1) (hb : d300030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243563, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243564 q = 1) (hb : d300031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243564, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243668 q = 1) (hb : d300038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243668, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83304 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243676 q = 1) (hb : d300039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243676, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243677 q = 1) (hb : d300040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243677, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243678 q = 1) (hb : d300041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243678, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243679 q = 1) (hb : d300042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243679, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243680 q = 1) (hb : d300043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243680, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83306 (p : Pattern) (ha : d243686 p = 1) (hb : d300049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d300044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83305 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d300045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d300046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d300047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d300048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d300049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83307 (p : Pattern) (ha : d243692 p = 1) (hb : d300055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d299936 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83276 q ha hb
    | true =>
      simp only [d242306, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83282 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d299963 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83288 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d299964 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d299991 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83294 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d299992 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d299993 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d300020 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83300 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d300021 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d300022 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d300023 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d300050 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83306 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d300051 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d300052 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d300053 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d300054 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d300055 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro83308 (p : Pattern) (ha : d243698 p = 1) (hb : d300061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d300056 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83307 q ha hb
    | true =>
      simp only [d243693, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d300057 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d300058 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d300059 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d300060 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d300061 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83309 (p : Pattern) (ha : d243704 p = 1) (hb : d300067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d300062 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83308 q ha hb
    | true =>
      simp only [d243699, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d300063 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d300064 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d300065 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d300066 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d300067 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83310 (p : Pattern) (ha : d243710 p = 1) (hb : d300073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d300068 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83309 q ha hb
    | true =>
      simp only [d243705, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d300069 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d300070 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d300071 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d300072 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d300073 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83311 (p : Pattern) (ha : d243716 p = 1) (hb : d300079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d300074 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83310 q ha hb
    | true =>
      simp only [d243711, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d300075 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d300076 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d300077 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d300078 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d300079 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83312 (p : Pattern) (ha : d243722 p = 1) (hb : d300085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d300080 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83311 q ha hb
    | true =>
      simp only [d243717, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d300081 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d300082 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d300083 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d300084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d300085 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83313 (p : Pattern) (ha : d243728 p = 1) (hb : d300091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d300086 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83312 q ha hb
    | true =>
      simp only [d243723, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d300087 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d300088 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d300089 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d300090 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d300091 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83314 (p : Pattern) (ha : d243734 p = 1) (hb : d300097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d300092 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83313 q ha hb
    | true =>
      simp only [d243729, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d300093 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d300094 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d300095 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d300096 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d300097 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83315 (p : Pattern) (ha : d245392 p = 1) (hb : d298159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245388 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245388, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245389 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245389, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245390 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245390, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245391 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245391, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245392 q = 1) (hb : d298159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245392, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83316 (p : Pattern) (ha : d245397 p = 1) (hb : d298166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245388 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245388, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245389 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245389, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245390 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245390, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245391 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245391, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245393 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245393, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245394 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245394, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245395 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245395, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245396 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245396, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245397 q = 1) (hb : d298166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245397, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83317 (p : Pattern) (ha : d245404 p = 1) (hb : d299887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245393 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245393, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245394 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245394, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245402 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245402, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245403 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245403, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d299887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83318 (p : Pattern) (ha : d245414 p = 1) (hb : d299897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245410 q = 1) (hb : d299893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245410, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d299894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245411, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d299895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d299896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d299897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83319 (p : Pattern) (ha : d245420 p = 1) (hb : d299903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245398 q = 1) (hb : d298167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83315 q ha hb
    | true =>
      simp only [d245398, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83316 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245399 q = 1) (hb : d298168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245399, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245400 q = 1) (hb : d299885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245400, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245401 q = 1) (hb : d299886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245401, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245405 q = 1) (hb : d299888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245405, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83317 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245406 q = 1) (hb : d299889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245406, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245407 q = 1) (hb : d299890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245407, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245408 q = 1) (hb : d299891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245408, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245409 q = 1) (hb : d299892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245409, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245415 q = 1) (hb : d299898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245415, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83318 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245416 q = 1) (hb : d299899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245416, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245417 q = 1) (hb : d299900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245417, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245418 q = 1) (hb : d299901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245418, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245419 q = 1) (hb : d299902 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245419, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245420 q = 1) (hb : d299903 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245420, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83320 (p : Pattern) (ha : d245426 p = 1) (hb : d299909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d245383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61343 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d245384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d245385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d245386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d245387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245421 q = 1) (hb : d299904 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245421, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83319 q ha hb
  have h8 (q : Pattern) (ha : d245422 q = 1) (hb : d299905 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245422, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245423 q = 1) (hb : d299906 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245423, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245424 q = 1) (hb : d299907 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245424, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245425 q = 1) (hb : d299908 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245425, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245426 q = 1) (hb : d299909 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d245426, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro83321 (p : Pattern) (ha : d245431 p = 1) (hb : d298326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245427 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245427, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245428 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245428, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245429 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245429, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245430 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245430, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245431 q = 1) (hb : d298326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245431, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83322 (p : Pattern) (ha : d245436 p = 1) (hb : d298336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245427 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245427, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245428 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245428, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245429 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245429, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245430 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245430, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245432 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245432, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245433 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245433, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245434 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245434, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245435 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245435, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245436 q = 1) (hb : d298336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245436, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83323 (p : Pattern) (ha : d245443 p = 1) (hb : d299912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245432 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245432, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245433 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245433, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245441 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245441, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245442 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245442, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d299912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83324 (p : Pattern) (ha : d245453 p = 1) (hb : d299923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245449 q = 1) (hb : d299919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245449, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d299920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245450, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d299921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d299922 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d299923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83325 (p : Pattern) (ha : d245459 p = 1) (hb : d299929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245437 q = 1) (hb : d298337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83321 q ha hb
    | true =>
      simp only [d245437, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83322 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245438 q = 1) (hb : d298338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245438, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245439 q = 1) (hb : d299910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245439, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245440 q = 1) (hb : d299911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245440, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245444 q = 1) (hb : d299913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245444, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83323 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31113 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245445 q = 1) (hb : d299914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245445, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245446 q = 1) (hb : d299915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245446, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245447 q = 1) (hb : d299916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245447, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245448 q = 1) (hb : d299917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245448, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245454 q = 1) (hb : d299924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245454, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83324 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245455 q = 1) (hb : d299925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245455, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245456 q = 1) (hb : d299926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245456, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245457 q = 1) (hb : d299927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245457, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245458 q = 1) (hb : d299928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245458, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245459 q = 1) (hb : d299929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245459, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83326 (p : Pattern) (ha : d245465 p = 1) (hb : d299935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d299930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83325 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d299931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d299932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d299933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d299934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d299935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83327 (p : Pattern) (ha : d245471 p = 1) (hb : d298576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245467 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245467, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245468 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245468, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245469 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245469, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245470 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245470, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245471 q = 1) (hb : d298576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245471, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245471, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83328 (p : Pattern) (ha : d245476 p = 1) (hb : d298586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245467 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245467, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245468 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245468, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245469 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245469, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245470 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245470, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245472 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245472, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245473 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245473, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245474 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245474, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245474, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245475 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245475, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245475, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245476 q = 1) (hb : d298586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245476, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245476, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83329 (p : Pattern) (ha : d245483 p = 1) (hb : d299939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245472 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245472, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245473 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245473, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245481 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245481, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245481, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245482 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245482, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245482, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245483 q = 1) (hb : d299939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245483, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83330 (p : Pattern) (ha : d245493 p = 1) (hb : d299950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245489 q = 1) (hb : d299946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245489, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31591 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245490 q = 1) (hb : d299947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245490, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245491 q = 1) (hb : d299948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245491, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245492 q = 1) (hb : d299949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245492, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245493 q = 1) (hb : d299950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245493, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83331 (p : Pattern) (ha : d245499 p = 1) (hb : d299956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245477 q = 1) (hb : d298587 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245477, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83327 q ha hb
    | true =>
      simp only [d245477, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83328 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245478 q = 1) (hb : d298588 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245478, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245478, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245479 q = 1) (hb : d299937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245479, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245480 q = 1) (hb : d299938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245480, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245484 q = 1) (hb : d299940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245484, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83329 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31470 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245485 q = 1) (hb : d299941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245485, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245486 q = 1) (hb : d299942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245486, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245487 q = 1) (hb : d299943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245487, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245488 q = 1) (hb : d299944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245488, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245494 q = 1) (hb : d299951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245494, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83330 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31607 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245495 q = 1) (hb : d299952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245495, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245496 q = 1) (hb : d299953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245496, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245497 q = 1) (hb : d299954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245497, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245498 q = 1) (hb : d299955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245498, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245499 q = 1) (hb : d299956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245499, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83332 (p : Pattern) (ha : d245505 p = 1) (hb : d299962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245500 q = 1) (hb : d299957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245500, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83331 q ha hb
  have h2 (q : Pattern) (ha : d245501 q = 1) (hb : d299958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245501, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245502 q = 1) (hb : d299959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245502, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245503 q = 1) (hb : d299960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245503, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245504 q = 1) (hb : d299961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245504, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245505 q = 1) (hb : d299962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245505, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83333 (p : Pattern) (ha : d245512 p = 1) (hb : d298890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245508 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245508, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245509 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245509, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245510 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245510, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245511 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245511, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245512 q = 1) (hb : d298890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83334 (p : Pattern) (ha : d245517 p = 1) (hb : d298900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245508 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245508, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245509 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245509, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245510 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245510, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245511 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245511, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245513 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245513, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245514 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245514, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245515 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245515, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245516 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245516, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245517 q = 1) (hb : d298900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245517, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83335 (p : Pattern) (ha : d245524 p = 1) (hb : d299967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245513 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245514, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d299967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83336 (p : Pattern) (ha : d245534 p = 1) (hb : d299978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245530 q = 1) (hb : d299974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d299975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245531, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d299976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d299977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d299978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83337 (p : Pattern) (ha : d245540 p = 1) (hb : d299984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245518 q = 1) (hb : d298901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83333 q ha hb
    | true =>
      simp only [d245518, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83334 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245519 q = 1) (hb : d298902 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245519, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245520 q = 1) (hb : d299965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245520, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245521 q = 1) (hb : d299966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245521, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245525 q = 1) (hb : d299968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245525, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83335 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245526 q = 1) (hb : d299969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245526, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245527 q = 1) (hb : d299970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245527, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245528 q = 1) (hb : d299971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245528, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245529 q = 1) (hb : d299972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245529, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245535 q = 1) (hb : d299979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245535, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83336 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245536 q = 1) (hb : d299980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245536, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245537 q = 1) (hb : d299981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245537, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245538 q = 1) (hb : d299982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245538, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245539 q = 1) (hb : d299983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245539, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245540 q = 1) (hb : d299984 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245540, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83338 (p : Pattern) (ha : d245546 p = 1) (hb : d299990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d299985 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83337 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d299986 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d299987 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d299988 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d299989 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d299990 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83339 (p : Pattern) (ha : d245554 p = 1) (hb : d299257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245550 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245550, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245551 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245551, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245552 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245552, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245553 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245553, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245554 q = 1) (hb : d299257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83340 (p : Pattern) (ha : d245559 p = 1) (hb : d299267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245550 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245550, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245551 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245551, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245552 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245552, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245553 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245553, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245555 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245555, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245556 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245556, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245557 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245557, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245558 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245558, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245559 q = 1) (hb : d299267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245559, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83341 (p : Pattern) (ha : d245566 p = 1) (hb : d299996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245555 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245555, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245556, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d299996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83342 (p : Pattern) (ha : d245576 p = 1) (hb : d300007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245572 q = 1) (hb : d300003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245572, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d300004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245573, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d300005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d300006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d300007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83343 (p : Pattern) (ha : d245582 p = 1) (hb : d300013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245560 q = 1) (hb : d299268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83339 q ha hb
    | true =>
      simp only [d245560, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83340 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245561 q = 1) (hb : d299269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245561, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245562 q = 1) (hb : d299994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245562, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245563 q = 1) (hb : d299995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245563, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245567 q = 1) (hb : d299997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245567, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83341 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245568 q = 1) (hb : d299998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245568, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245569 q = 1) (hb : d299999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245569, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245570 q = 1) (hb : d300000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245570, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245571 q = 1) (hb : d300001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245571, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245577 q = 1) (hb : d300008 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245577, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83342 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245578 q = 1) (hb : d300009 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245578, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245579 q = 1) (hb : d300010 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245579, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245580 q = 1) (hb : d300011 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245580, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245581 q = 1) (hb : d300012 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245581, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245582 q = 1) (hb : d300013 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245582, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83344 (p : Pattern) (ha : d245588 p = 1) (hb : d300019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d300014 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83343 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d300015 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d300016 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d300017 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d300018 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d300019 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83345 (p : Pattern) (ha : d245597 p = 1) (hb : d299595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245593 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245593, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245594 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245594, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245595 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245595, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245596 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245596, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245597 q = 1) (hb : d299595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245597, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245597, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83346 (p : Pattern) (ha : d245602 p = 1) (hb : d299605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245593 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245593, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245594 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245594, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245595 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245595, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245596 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245596, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245598 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245598, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245599 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245599, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245600 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245600, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245600, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245601 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245601, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245601, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245602 q = 1) (hb : d299605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245602, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245602, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83347 (p : Pattern) (ha : d245609 p = 1) (hb : d300026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245598 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245598, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245599 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245599, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245607 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245607, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245607, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245608 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245608, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245608, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d300026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83348 (p : Pattern) (ha : d245619 p = 1) (hb : d300037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245615 q = 1) (hb : d300033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245615, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245615, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245616 q = 1) (hb : d300034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245616, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245616, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245617 q = 1) (hb : d300035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245617, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245617, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245618 q = 1) (hb : d300036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245618, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245618, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245619 q = 1) (hb : d300037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245619, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245619, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83349 (p : Pattern) (ha : d245625 p = 1) (hb : d300043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245603 q = 1) (hb : d299606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245603, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83345 q ha hb
    | true =>
      simp only [d245603, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83346 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245604 q = 1) (hb : d299607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245604, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245604, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245605 q = 1) (hb : d300024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245605, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245605, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245606 q = 1) (hb : d300025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245606, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245606, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245610 q = 1) (hb : d300027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245610, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245610, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83347 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245611 q = 1) (hb : d300028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245611, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245611, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245612 q = 1) (hb : d300029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245612, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245612, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245613 q = 1) (hb : d300030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245613, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245613, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245614 q = 1) (hb : d300031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245614, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245614, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245620 q = 1) (hb : d300038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245620, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245620, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83348 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245621 q = 1) (hb : d300039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245621, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245621, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245622 q = 1) (hb : d300040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245622, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245622, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245623 q = 1) (hb : d300041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245623, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245623, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245624 q = 1) (hb : d300042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245624, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245624, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245625 q = 1) (hb : d300043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245625, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245625, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83350 (p : Pattern) (ha : d245631 p = 1) (hb : d300049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245626 q = 1) (hb : d300044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245626, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245626, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83349 q ha hb
  have h2 (q : Pattern) (ha : d245627 q = 1) (hb : d300045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245627, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245627, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245628 q = 1) (hb : d300046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245628, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245628, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245629 q = 1) (hb : d300047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245629, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245629, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245630 q = 1) (hb : d300048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245630, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245630, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245631 q = 1) (hb : d300049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245631, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245631, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83351 (p : Pattern) (ha : d245637 p = 1) (hb : d300055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245466 q = 1) (hb : d299936 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245466, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83320 q ha hb
    | true =>
      simp only [d245466, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83326 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245506 q = 1) (hb : d299963 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245506, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245506, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83332 q ha hb
  have h3 (q : Pattern) (ha : d245507 q = 1) (hb : d299964 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245507, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245507, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245547 q = 1) (hb : d299991 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245547, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245547, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83338 q ha hb
  have h5 (q : Pattern) (ha : d245548 q = 1) (hb : d299992 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245548, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245548, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245549 q = 1) (hb : d299993 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245549, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245549, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245589 q = 1) (hb : d300020 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245589, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245589, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83344 q ha hb
  have h8 (q : Pattern) (ha : d245590 q = 1) (hb : d300021 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245590, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245590, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245591 q = 1) (hb : d300022 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245591, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245591, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245592 q = 1) (hb : d300023 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245592, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245592, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245632 q = 1) (hb : d300050 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245632, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245632, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83350 q ha hb
  have h12 (q : Pattern) (ha : d245633 q = 1) (hb : d300051 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245633, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245633, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245634 q = 1) (hb : d300052 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245634, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245634, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245635 q = 1) (hb : d300053 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245635, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245635, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245636 q = 1) (hb : d300054 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245636, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245636, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245637 q = 1) (hb : d300055 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245637, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245637, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro83352 (p : Pattern) (ha : d245643 p = 1) (hb : d300061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245638 q = 1) (hb : d300056 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245638, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83351 q ha hb
    | true =>
      simp only [d245638, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245639 q = 1) (hb : d300057 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245639, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245639, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245640 q = 1) (hb : d300058 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245640, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245640, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245641 q = 1) (hb : d300059 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245641, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245641, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245642 q = 1) (hb : d300060 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245642, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245642, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245643 q = 1) (hb : d300061 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245643, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245643, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83353 (p : Pattern) (ha : d245649 p = 1) (hb : d300067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245644 q = 1) (hb : d300062 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245644, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83352 q ha hb
    | true =>
      simp only [d245644, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245645 q = 1) (hb : d300063 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245645, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245645, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245646 q = 1) (hb : d300064 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245646, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245646, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245647 q = 1) (hb : d300065 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245647, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245647, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245648 q = 1) (hb : d300066 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245648, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245648, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245649 q = 1) (hb : d300067 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245649, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245649, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83354 (p : Pattern) (ha : d245655 p = 1) (hb : d300073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245650 q = 1) (hb : d300068 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245650, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83353 q ha hb
    | true =>
      simp only [d245650, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245651 q = 1) (hb : d300069 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245651, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245651, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245652 q = 1) (hb : d300070 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245652, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245652, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245653 q = 1) (hb : d300071 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245653, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245653, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245654 q = 1) (hb : d300072 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245654, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245654, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245655 q = 1) (hb : d300073 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245655, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245655, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83355 (p : Pattern) (ha : d245661 p = 1) (hb : d300079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245656 q = 1) (hb : d300074 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245656, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83354 q ha hb
    | true =>
      simp only [d245656, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245657 q = 1) (hb : d300075 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245657, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245657, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245658 q = 1) (hb : d300076 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245658, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245658, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245659 q = 1) (hb : d300077 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245659, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245659, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245660 q = 1) (hb : d300078 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245660, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245660, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245661 q = 1) (hb : d300079 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245661, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245661, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83356 (p : Pattern) (ha : d245667 p = 1) (hb : d300085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245662 q = 1) (hb : d300080 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245662, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83355 q ha hb
    | true =>
      simp only [d245662, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245663 q = 1) (hb : d300081 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245663, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245663, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245664 q = 1) (hb : d300082 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245664, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245664, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245665 q = 1) (hb : d300083 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245665, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245665, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245666 q = 1) (hb : d300084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245666, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245666, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245667 q = 1) (hb : d300085 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245667, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245667, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83357 (p : Pattern) (ha : d245673 p = 1) (hb : d300091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245668 q = 1) (hb : d300086 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245668, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83356 q ha hb
    | true =>
      simp only [d245668, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245669 q = 1) (hb : d300087 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245669, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245669, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245670 q = 1) (hb : d300088 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245670, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245670, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245671 q = 1) (hb : d300089 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245671, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245671, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245672 q = 1) (hb : d300090 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245672, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245672, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245673 q = 1) (hb : d300091 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245673, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245673, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83358 (p : Pattern) (ha : d245679 p = 1) (hb : d300097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245674 q = 1) (hb : d300092 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245674, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83357 q ha hb
    | true =>
      simp only [d245674, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245675 q = 1) (hb : d300093 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245675, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245675, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245676 q = 1) (hb : d300094 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245676, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245676, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245677 q = 1) (hb : d300095 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245677, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245677, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245678 q = 1) (hb : d300096 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245678, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245678, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245679 q = 1) (hb : d300097 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245679, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245679, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83359 (p : Pattern) (ha : d33214 p = 1) (hb : d282283 p = 1) : d38813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17 q = 1) (hb : d261984 q = 1) : d17 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33214 q = 1) (hb : d282283 q = 1) : d38813 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33214, d282283, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33214, d282283, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83360 (p : Pattern) (ha : d33220 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d33218 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33219 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d22 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d23 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d33220 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33220, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33220, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro83361 (p : Pattern) (ha : d33226 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33221 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
    | true =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33222 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33223 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33224 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33224, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33225 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33225, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33225, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33226 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33226, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33226, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83362 (p : Pattern) (ha : d33232 p = 1) (hb : d282284 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33227 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
    | true =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h2 (q : Pattern) (ha : d33228 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33229 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33230 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33230, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33231 q = 1) (hb : d282284 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33231, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33231, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33232 q = 1) (hb : d282284 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33232, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33232, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83363 (p : Pattern) (ha : d33238 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33236 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33237 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33237, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33238 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33238, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33238, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83364 (p : Pattern) (ha : d265915 p = 1) (hb : d282284 p = 1) : d257212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33239 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
    | true =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h9 (q : Pattern) (ha : d265911 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265911, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265912 q = 1) (hb : d282284 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265912, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265913 q = 1) (hb : d282284 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265913, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265914 q = 1) (hb : d282284 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265914, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265915 q = 1) (hb : d282284 q = 1) : d257212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265915, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265915, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83365 (p : Pattern) (ha : d33245 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33236 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33237 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33237, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33245 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33245, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33245, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83366 (p : Pattern) (ha : d265920 p = 1) (hb : d282284 p = 1) : d257219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33239 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
    | true =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h9 (q : Pattern) (ha : d265911 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265911, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265912 q = 1) (hb : d282284 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265912, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265913 q = 1) (hb : d282284 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265913, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265914 q = 1) (hb : d282284 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265914, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72081 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72082 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33246 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
    | true =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h23 (q : Pattern) (ha : d265916 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265916, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d265917 q = 1) (hb : d282284 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d265917, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d265918 q = 1) (hb : d282284 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265918, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265918, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d265919 q = 1) (hb : d282284 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265919, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265919, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d265920 q = 1) (hb : d282284 q = 1) : d257219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265920, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265920, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro83367 (p : Pattern) (ha : d265927 p = 1) (hb : d282284 p = 1) : d257224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33246 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
    | true =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h2 (q : Pattern) (ha : d265916 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265916, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265917 q = 1) (hb : d282284 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265917, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265925 q = 1) (hb : d282284 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265925, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265925, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265926 q = 1) (hb : d282284 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265926, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265926, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265927 q = 1) (hb : d282284 q = 1) : d257224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265927, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265927, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83368 (p : Pattern) (ha : d33269 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33264 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
  have h2 (q : Pattern) (ha : d33221 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
    | true =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33265 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33265, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33222 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33266 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33266, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33267 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33267, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33268 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33268, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33268, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33269 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33269, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33269, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83369 (p : Pattern) (ha : d33275 p = 1) (hb : d282284 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33270 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
    | true =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h2 (q : Pattern) (ha : d33271 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33272 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33273 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33273, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33274 q = 1) (hb : d282284 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33274, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33274, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33275 q = 1) (hb : d282284 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33275, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33275, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83370 (p : Pattern) (ha : d33281 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83369 q ha hb
    | true =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72060 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33278 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33278, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33278, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33279 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33279, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33279, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33280 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33280, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33280, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33281 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33281, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33281, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83371 (p : Pattern) (ha : d265937 p = 1) (hb : d282284 p = 1) : d257253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33282 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83370 q ha hb
    | true =>
      simp only [d33282, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
  have h2 (q : Pattern) (ha : d265933 q = 1) (hb : d282284 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265933, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265933, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265934 q = 1) (hb : d282284 q = 1) : d257250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265934, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265934, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265935 q = 1) (hb : d282284 q = 1) : d257251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265935, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265935, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265936 q = 1) (hb : d282284 q = 1) : d257252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265936, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265936, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265937 q = 1) (hb : d282284 q = 1) : d257253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265937, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265937, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83372 (p : Pattern) (ha : d265943 p = 1) (hb : d282284 p = 1) : d257259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72064 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72064 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72065 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265921 q = 1) (hb : d282284 q = 1) : d257220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265921, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83364 q ha hb
    | true =>
      simp only [d265921, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83366 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72066 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d265922 q = 1) (hb : d282284 q = 1) : d257221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265922, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265922, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265923 q = 1) (hb : d282284 q = 1) : d257222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265923, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265923, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d265924 q = 1) (hb : d282284 q = 1) : d257223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265924, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265924, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265928 q = 1) (hb : d282284 q = 1) : d257225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265928, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265928, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83367 q ha hb
  have h12 (q : Pattern) (ha : d265929 q = 1) (hb : d282284 q = 1) : d257226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265929, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265929, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d265930 q = 1) (hb : d282284 q = 1) : d257227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265930, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265930, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265931 q = 1) (hb : d282284 q = 1) : d257228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265931, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265931, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d265932 q = 1) (hb : d282284 q = 1) : d257229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265932, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265932, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265938 q = 1) (hb : d282284 q = 1) : d257254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265938, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265938, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83371 q ha hb
  have h17 (q : Pattern) (ha : d265939 q = 1) (hb : d282284 q = 1) : d257255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265939, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265939, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d265940 q = 1) (hb : d282284 q = 1) : d257256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265940, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265940, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d265941 q = 1) (hb : d282284 q = 1) : d257257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265941, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265941, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d265942 q = 1) (hb : d282284 q = 1) : d257258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265942, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d265942, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d265943 q = 1) (hb : d282284 q = 1) : d257259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265943, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265943, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro83373 (p : Pattern) (ha : d33303 p = 1) (hb : d282284 p = 1) : d257269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33239 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
    | true =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d33299 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33300 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33301 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33302 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33303 q = 1) (hb : d282284 q = 1) : d257269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33303, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33303, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83374 (p : Pattern) (ha : d33310 p = 1) (hb : d282284 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33239 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
    | true =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d33299 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33300 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33301 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33302 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33246 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
    | true =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h7 (q : Pattern) (ha : d33306 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33307 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33307, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33308 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33309 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33310 q = 1) (hb : d282284 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33310, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33310, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83375 (p : Pattern) (ha : d33421 p = 1) (hb : d282284 p = 1) : d257340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33239 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
    | true =>
      simp only [d33239, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d33299 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33300 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33300, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33301 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33302 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33421 q = 1) (hb : d282284 q = 1) : d257340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33421, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33421, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83376 (p : Pattern) (ha : d33315 p = 1) (hb : d282284 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33236 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33314 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33315 q = 1) (hb : d282284 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33315, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33315, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83377 (p : Pattern) (ha : d33322 p = 1) (hb : d282284 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33320 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33321 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33321, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33322 q = 1) (hb : d282284 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33322, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33322, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83378 (p : Pattern) (ha : d33327 p = 1) (hb : d282283 p = 1) : d285865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33213 q = 1) (hb : d261984 q = 1) : d33213 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33327 q = 1) (hb : d282283 q = 1) : d285865 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33327, d282283, d285865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33327, d282283, d285865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83379 (p : Pattern) (ha : d33333 p = 1) (hb : d282284 p = 1) : d285871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33330 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33331 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33332 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d33218 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33219 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d33333 q = 1) (hb : d282284 q = 1) : d285871 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33333, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33333, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83380 (p : Pattern) (ha : d33341 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33339 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d33340 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d22 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d23 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d33341 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33341, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33341, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro83381 (p : Pattern) (ha : d33347 p = 1) (hb : d282284 p = 1) : d285877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
    | true =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33221 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
    | true =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33222 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33223 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33224 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33224, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33338 q = 1) (hb : d282284 q = 1) : d285876 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33338, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33338, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33344 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33345 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33346 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33346, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33347 q = 1) (hb : d282284 q = 1) : d285877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33347, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33347, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83382 (p : Pattern) (ha : d33353 p = 1) (hb : d282284 p = 1) : d285883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83381 q ha hb
    | true =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33227 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
    | true =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h5 (q : Pattern) (ha : d33228 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33229 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33351 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33230 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33230, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33352 q = 1) (hb : d282284 q = 1) : d285882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33352, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33352, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33353 q = 1) (hb : d282284 q = 1) : d285883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33353, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33353, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro83383 (p : Pattern) (ha : d33359 p = 1) (hb : d282284 p = 1) : d285889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83382 q ha hb
    | true =>
      simp only [d33354, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33359 q = 1) (hb : d282284 q = 1) : d285889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33359, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33359, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83384 (p : Pattern) (ha : d33392 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33392 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33392, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33392, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83385 (p : Pattern) (ha : d265953 p = 1) (hb : d282284 p = 1) : d285895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33316 q = 1) (hb : d282284 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83376 q ha hb
    | true =>
      simp only [d33316, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
  have h2 (q : Pattern) (ha : d33317 q = 1) (hb : d282284 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33318 q = 1) (hb : d282284 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33318, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33319 q = 1) (hb : d282284 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33323 q = 1) (hb : d282284 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83377 q ha hb
    | true =>
      simp only [d33323, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
  have h6 (q : Pattern) (ha : d33324 q = 1) (hb : d282284 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33325 q = 1) (hb : d282284 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33325, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33360 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83383 q ha hb
    | true =>
      simp only [d33360, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
  have h9 (q : Pattern) (ha : d265949 q = 1) (hb : d282284 q = 1) : d285891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265949, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33393 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83384 q ha hb
    | true =>
      simp only [d33393, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33394 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33394, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265950 q = 1) (hb : d282284 q = 1) : d285892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265950, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265951 q = 1) (hb : d282284 q = 1) : d285893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265951, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265952 q = 1) (hb : d282284 q = 1) : d285894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265952, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265953 q = 1) (hb : d282284 q = 1) : d285895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d285895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d285895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83386 (p : Pattern) (ha : d33399 p = 1) (hb : d282284 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33236 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33236, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33314 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33399 q = 1) (hb : d282284 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33399, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33399, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83387 (p : Pattern) (ha : d33404 p = 1) (hb : d282284 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33235 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33320 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33321 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33321, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33404 q = 1) (hb : d282284 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33404, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33404, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83388 (p : Pattern) (ha : d33408 p = 1) (hb : d282284 p = 1) : d285896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83382 q ha hb
    | true =>
      simp only [d33354, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33408 q = 1) (hb : d282284 q = 1) : d285896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33408, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33408, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83389 (p : Pattern) (ha : d33413 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83362 q ha hb
    | true =>
      simp only [d33233, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33413 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33413, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33413, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83390 (p : Pattern) (ha : d265958 p = 1) (hb : d282284 p = 1) : d285902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33316 q = 1) (hb : d282284 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83376 q ha hb
    | true =>
      simp only [d33316, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
  have h2 (q : Pattern) (ha : d33317 q = 1) (hb : d282284 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33318 q = 1) (hb : d282284 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33318, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33319 q = 1) (hb : d282284 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33323 q = 1) (hb : d282284 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83377 q ha hb
    | true =>
      simp only [d33323, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
  have h6 (q : Pattern) (ha : d33324 q = 1) (hb : d282284 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33325 q = 1) (hb : d282284 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33325, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33360 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83383 q ha hb
    | true =>
      simp only [d33360, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83363 q ha hb
  have h9 (q : Pattern) (ha : d265949 q = 1) (hb : d282284 q = 1) : d285891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265949, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33393 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83384 q ha hb
    | true =>
      simp only [d33393, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33394 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33394, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265950 q = 1) (hb : d282284 q = 1) : d285892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265950, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265951 q = 1) (hb : d282284 q = 1) : d285893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265951, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265952 q = 1) (hb : d282284 q = 1) : d285894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265952, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33400 q = 1) (hb : d282284 q = 1) : d257324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33400, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83386 q ha hb
    | true =>
      simp only [d33400, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72081 q ha hb
  have h16 (q : Pattern) (ha : d33401 q = 1) (hb : d282284 q = 1) : d257325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33401, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33401, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33402 q = 1) (hb : d282284 q = 1) : d257326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33402, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33402, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33403 q = 1) (hb : d282284 q = 1) : d257327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33403, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33403, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33405 q = 1) (hb : d282284 q = 1) : d257329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33405, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83387 q ha hb
    | true =>
      simp only [d33405, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72082 q ha hb
  have h20 (q : Pattern) (ha : d33406 q = 1) (hb : d282284 q = 1) : d257330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33406, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33406, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d33407 q = 1) (hb : d282284 q = 1) : d257331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33407, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33407, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33409 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83388 q ha hb
    | true =>
      simp only [d33409, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
  have h23 (q : Pattern) (ha : d265954 q = 1) (hb : d282284 q = 1) : d285898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265954, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33414 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83389 q ha hb
    | true =>
      simp only [d33414, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d33415 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33415, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d265955 q = 1) (hb : d282284 q = 1) : d285899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d265955, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d265956 q = 1) (hb : d282284 q = 1) : d285900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d285900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265956, d285900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d265957 q = 1) (hb : d282284 q = 1) : d285901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d285901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265957, d285901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d265958 q = 1) (hb : d282284 q = 1) : d285902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d285902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265958, d285902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro83391 (p : Pattern) (ha : d265965 p = 1) (hb : d282284 p = 1) : d285909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33409 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83388 q ha hb
    | true =>
      simp only [d33409, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
  have h2 (q : Pattern) (ha : d265954 q = 1) (hb : d282284 q = 1) : d285898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265954, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33414 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83389 q ha hb
    | true =>
      simp only [d33414, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33415 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33415, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d282284 q = 1) : d285899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265955, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d282284 q = 1) : d285907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d285907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d285907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d282284 q = 1) : d285908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d285908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d285908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d282284 q = 1) : d285909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d285909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d285909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83392 (p : Pattern) (ha : d33444 p = 1) (hb : d282284 p = 1) : d285920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
    | true =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33264 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
  have h8 (q : Pattern) (ha : d33221 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83360 q ha hb
    | true =>
      simp only [d33221, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33265 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33265, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33222 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33222, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33266 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33266, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33267 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33267, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33438 q = 1) (hb : d282284 q = 1) : d285919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33438, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33438, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33439 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
  have h15 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33440 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33441 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33442 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33443 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33443, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d33444 q = 1) (hb : d282284 q = 1) : d285920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33444, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33444, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro83393 (p : Pattern) (ha : d33450 p = 1) (hb : d282284 p = 1) : d285926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83392 q ha hb
    | true =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33270 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
    | true =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h5 (q : Pattern) (ha : d33271 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33272 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33448 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33273 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33273, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33449 q = 1) (hb : d282284 q = 1) : d285925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33449, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33449, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33450 q = 1) (hb : d282284 q = 1) : d285926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33450, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33450, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro83394 (p : Pattern) (ha : d33456 p = 1) (hb : d282284 p = 1) : d285932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33451 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33451, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83393 q ha hb
    | true =>
      simp only [d33451, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33452 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33452, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33452, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33276 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83369 q ha hb
    | true =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33277 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33453 q = 1) (hb : d282284 q = 1) : d285929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33453, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33453, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33454 q = 1) (hb : d282284 q = 1) : d285930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33454, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33454, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33455 q = 1) (hb : d282284 q = 1) : d285931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33455, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33455, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33456 q = 1) (hb : d282284 q = 1) : d285932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33456, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33456, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83395 (p : Pattern) (ha : d33481 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83369 q ha hb
    | true =>
      simp only [d33276, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33478 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33478, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33478, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33479 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33479, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33479, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33480 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33480, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33480, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33481 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33481, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33481, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83396 (p : Pattern) (ha : d265975 p = 1) (hb : d282284 p = 1) : d285938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33457 q = 1) (hb : d282284 q = 1) : d285933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33457, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83394 q ha hb
    | true =>
      simp only [d33457, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83370 q ha hb
  have h2 (q : Pattern) (ha : d265971 q = 1) (hb : d282284 q = 1) : d285934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d285934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265971, d285934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33482 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33482, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83395 q ha hb
    | true =>
      simp only [d33482, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33483 q = 1) (hb : d282284 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33483, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33483, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d282284 q = 1) : d285935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d285935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265972, d285935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d282284 q = 1) : d285936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d285936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d285936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d282284 q = 1) : d285937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d285937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d285937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d282284 q = 1) : d285938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d285938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d285938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83397 (p : Pattern) (ha : d265981 p = 1) (hb : d282284 p = 1) : d285944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33304 q = 1) (hb : d282284 q = 1) : d257270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33304, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33304, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83373 q ha hb
  have h2 (q : Pattern) (ha : d33305 q = 1) (hb : d282284 q = 1) : d257271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33305, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33305, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33311 q = 1) (hb : d282284 q = 1) : d257277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83373 q ha hb
    | true =>
      simp only [d33311, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83374 q ha hb
  have h4 (q : Pattern) (ha : d33312 q = 1) (hb : d282284 q = 1) : d257278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33312, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33313 q = 1) (hb : d282284 q = 1) : d257279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33313, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33313, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265959 q = 1) (hb : d282284 q = 1) : d285903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d285903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83385 q ha hb
    | true =>
      simp only [d265959, d285903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83390 q ha hb
  have h7 (q : Pattern) (ha : d33422 q = 1) (hb : d282284 q = 1) : d257341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33422, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83375 q ha hb
    | true =>
      simp only [d33422, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72065 q ha hb
  have h8 (q : Pattern) (ha : d265960 q = 1) (hb : d282284 q = 1) : d285904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d285904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265960, d285904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265961 q = 1) (hb : d282284 q = 1) : d285905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d285905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265961, d285905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d265962 q = 1) (hb : d282284 q = 1) : d285906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d285906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265962, d285906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265966 q = 1) (hb : d282284 q = 1) : d285910 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d285910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265966, d285910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83391 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72088 q ha hb
  have h13 (q : Pattern) (ha : d265967 q = 1) (hb : d282284 q = 1) : d285911 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d285911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265967, d285911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265968 q = 1) (hb : d282284 q = 1) : d285912 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d285912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265968, d285912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d265969 q = 1) (hb : d282284 q = 1) : d285913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d285913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265969, d285913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d265970 q = 1) (hb : d282284 q = 1) : d285914 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d285914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265970, d285914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265976 q = 1) (hb : d282284 q = 1) : d285939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d285939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265976, d285939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83396 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72089 q ha hb
  have h19 (q : Pattern) (ha : d265977 q = 1) (hb : d282284 q = 1) : d285940 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d285940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265977, d285940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d265978 q = 1) (hb : d282284 q = 1) : d285941 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d285941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d265978, d285941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d265979 q = 1) (hb : d282284 q = 1) : d285942 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d285942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d265979, d285942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d265980 q = 1) (hb : d282284 q = 1) : d285943 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d285943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265980, d285943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d265981 q = 1) (hb : d282284 q = 1) : d285944 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d285944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265981, d285944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro83398 (p : Pattern) (ha : d265987 p = 1) (hb : d282284 p = 1) : d285950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72063 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265944 q = 1) (hb : d282284 q = 1) : d257260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265944, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265944, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83372 q ha hb
  have h6 (q : Pattern) (ha : d265945 q = 1) (hb : d282284 q = 1) : d257261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265945, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265945, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265946 q = 1) (hb : d282284 q = 1) : d257262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265946, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265946, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265947 q = 1) (hb : d282284 q = 1) : d257263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265947, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265947, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265948 q = 1) (hb : d282284 q = 1) : d257264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265948, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265948, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265982 q = 1) (hb : d282284 q = 1) : d285945 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d285945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265982, d285945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83397 q ha hb
  have h11 (q : Pattern) (ha : d265983 q = 1) (hb : d282284 q = 1) : d285946 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d285946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265983, d285946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265984 q = 1) (hb : d282284 q = 1) : d285947 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d285947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265984, d285947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265985 q = 1) (hb : d282284 q = 1) : d285948 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d285948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265985, d285948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265986 q = 1) (hb : d282284 q = 1) : d285949 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d285949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265986, d285949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265987 q = 1) (hb : d282284 q = 1) : d285950 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d285950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265987, d285950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83399 (p : Pattern) (ha : d33502 p = 1) (hb : d282284 p = 1) : d285883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83381 q ha hb
    | true =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33227 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
    | true =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h5 (q : Pattern) (ha : d33228 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33229 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33351 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33500 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33500, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33501 q = 1) (hb : d282284 q = 1) : d285882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33501, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33501, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33502 q = 1) (hb : d282284 q = 1) : d285883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33502, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33502, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83400 (p : Pattern) (ha : d33506 p = 1) (hb : d282284 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33227 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
    | true =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h2 (q : Pattern) (ha : d33228 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33229 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33500 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33500, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33505 q = 1) (hb : d282284 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33505, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33505, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33506 q = 1) (hb : d282284 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33506, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33506, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83401 (p : Pattern) (ha : d33512 p = 1) (hb : d282284 p = 1) : d285889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33512 q = 1) (hb : d282284 q = 1) : d285889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33512, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33512, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83402 (p : Pattern) (ha : d33516 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33516 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33516, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33516, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83403 (p : Pattern) (ha : d33522 p = 1) (hb : d282284 p = 1) : d285955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83401 q ha hb
    | true =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83402 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33522 q = 1) (hb : d282284 q = 1) : d285955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33522, d285955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33522, d285955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83404 (p : Pattern) (ha : d33525 p = 1) (hb : d282284 p = 1) : d285896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33525 q = 1) (hb : d282284 q = 1) : d285896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33525, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33525, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83405 (p : Pattern) (ha : d33526 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33526 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33526, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33526, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83406 (p : Pattern) (ha : d33532 p = 1) (hb : d282284 p = 1) : d285962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83401 q ha hb
    | true =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83402 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33527 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83404 q ha hb
    | true =>
      simp only [d33527, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83405 q ha hb
  have h7 (q : Pattern) (ha : d33528 q = 1) (hb : d282284 q = 1) : d285958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33529 q = 1) (hb : d282284 q = 1) : d285959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33529, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33530 q = 1) (hb : d282284 q = 1) : d285960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33531 q = 1) (hb : d282284 q = 1) : d285961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33532 q = 1) (hb : d282284 q = 1) : d285962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33532, d285962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33532, d285962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83407 (p : Pattern) (ha : d33688 p = 1) (hb : d282284 p = 1) : d286044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83401 q ha hb
    | true =>
      simp only [d33517, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83402 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33683 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83402 q ha hb
    | true =>
      simp only [d33683, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33684 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33685 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33685, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33686 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33687 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33688 q = 1) (hb : d282284 q = 1) : d286044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33688, d286044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33688, d286044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83408 (p : Pattern) (ha : d33694 p = 1) (hb : d282284 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33683 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83402 q ha hb
    | true =>
      simp only [d33683, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33684 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33685 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33685, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33686 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33687 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33689 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83405 q ha hb
    | true =>
      simp only [d33689, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33690 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33691 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33691, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33692 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33693 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33694 q = 1) (hb : d282284 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33694, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33694, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83409 (p : Pattern) (ha : d33703 p = 1) (hb : d282284 p = 1) : d257490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33689 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83405 q ha hb
    | true =>
      simp only [d33689, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33690 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33691 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33691, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33692 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33693 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33703 q = 1) (hb : d282284 q = 1) : d257490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33703, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33703, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83410 (p : Pattern) (ha : d33746 p = 1) (hb : d282284 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33270 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
    | true =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h2 (q : Pattern) (ha : d33271 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33272 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33736 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33736, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33736, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33745 q = 1) (hb : d282284 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33745, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33745, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33746 q = 1) (hb : d282284 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33746, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33746, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83411 (p : Pattern) (ha : d33802 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33747 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33747, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83410 q ha hb
    | true =>
      simp only [d33747, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33748 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33748, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33748, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33799 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33799, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33799, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33800 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33800, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33800, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33801 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33801, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33801, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33802 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33802, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33802, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83412 (p : Pattern) (ha : d33808 p = 1) (hb : d282284 p = 1) : d257536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33803 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33803, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83411 q ha hb
    | true =>
      simp only [d33803, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33804 q = 1) (hb : d282284 q = 1) : d257532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33804, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33804, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33805 q = 1) (hb : d282284 q = 1) : d257533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33805, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33805, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33806 q = 1) (hb : d282284 q = 1) : d257534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33806, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33806, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33807 q = 1) (hb : d282284 q = 1) : d257535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33807, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33807, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33808 q = 1) (hb : d282284 q = 1) : d257536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33808, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33808, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83413 (p : Pattern) (ha : d33537 p = 1) (hb : d282284 p = 1) : d285967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33536 q = 1) (hb : d282284 q = 1) : d285966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33536, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33536, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33537 q = 1) (hb : d282284 q = 1) : d285967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33537, d285967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33537, d285967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83414 (p : Pattern) (ha : d33539 p = 1) (hb : d282284 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33538 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33538, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33538, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33539 q = 1) (hb : d282284 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33539, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33539, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83415 (p : Pattern) (ha : d33546 p = 1) (hb : d282284 p = 1) : d285974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33544 q = 1) (hb : d282284 q = 1) : d285972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33544, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33544, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33545 q = 1) (hb : d282284 q = 1) : d285973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33545, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33545, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33546 q = 1) (hb : d282284 q = 1) : d285974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33546, d285974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33546, d285974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83416 (p : Pattern) (ha : d33549 p = 1) (hb : d282284 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33547 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33547, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33547, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33548 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33548, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33548, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33549 q = 1) (hb : d282284 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33549, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33549, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83417 (p : Pattern) (ha : d33555 p = 1) (hb : d282283 p = 1) : d286611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33553 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33554 q = 1) (hb : d261984 q = 1) : d33554 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33555 q = 1) (hb : d282283 q = 1) : d286611 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33555, d282283, d286611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33555, d282283, d286611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83418 (p : Pattern) (ha : d33560 p = 1) (hb : d282283 p = 1) : d316228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33559 q = 1) (hb : d261984 q = 1) : d33559 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33560 q = 1) (hb : d282283 q = 1) : d316228 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33560, d282283, d316228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33560, d282283, d316228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83419 (p : Pattern) (ha : d33566 p = 1) (hb : d282284 p = 1) : d316234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d282284 q = 1) : d286612 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83417 q ha hb
    | true =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33557 q = 1) (hb : d282284 q = 1) : d286613 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33558 q = 1) (hb : d282284 q = 1) : d316227 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33561 q = 1) (hb : d282284 q = 1) : d316229 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33561, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83418 q ha hb
    | true =>
      simp only [d33561, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33562 q = 1) (hb : d282284 q = 1) : d316230 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33562, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33562, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d33563 q = 1) (hb : d282284 q = 1) : d316231 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33563, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33563, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33564 q = 1) (hb : d282284 q = 1) : d316232 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33564, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33564, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33565 q = 1) (hb : d282284 q = 1) : d316233 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33565, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33565, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d33330 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d33331 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33332 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d33566 q = 1) (hb : d282284 q = 1) : d316234 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33566, d316234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33566, d316234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro83420 (p : Pattern) (ha : d33571 p = 1) (hb : d282284 p = 1) : d285871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33330 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33331 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33331, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33332 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33332, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d33339 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d33340 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d33571 q = 1) (hb : d282284 q = 1) : d285871 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33571, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33571, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro83421 (p : Pattern) (ha : d33579 p = 1) (hb : d282284 p = 1) : d285993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33330 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33330, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33577 q = 1) (hb : d282284 q = 1) : d285991 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33577, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33577, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d33578 q = 1) (hb : d282284 q = 1) : d285992 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33578, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33578, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33339 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33339, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d33340 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33340, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d33579 q = 1) (hb : d282284 q = 1) : d285993 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33579, d285993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33579, d285993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro83422 (p : Pattern) (ha : d33585 p = 1) (hb : d282284 p = 1) : d316240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33567 q = 1) (hb : d282284 q = 1) : d316235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
    | true =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33568 q = 1) (hb : d282284 q = 1) : d316236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33569 q = 1) (hb : d282284 q = 1) : d316237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33569, d316237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33569, d316237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33570 q = 1) (hb : d282284 q = 1) : d316238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33570, d316238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33570, d316238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33572 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
    | true =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33573 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33574 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33574, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33574, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33575 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33575, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33575, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33576 q = 1) (hb : d282284 q = 1) : d316239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33576, d316239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33576, d316239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33582 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33583 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33344 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33345 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33584 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33584, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33584, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33585 q = 1) (hb : d282284 q = 1) : d316240 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33585, d316240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33585, d316240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83423 (p : Pattern) (ha : d33589 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33344 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33345 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33345, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33346 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33346, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33589 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33589, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33589, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83424 (p : Pattern) (ha : d33595 p = 1) (hb : d282284 p = 1) : d316246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33586 q = 1) (hb : d282284 q = 1) : d316241 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33586, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83422 q ha hb
    | true =>
      simp only [d33586, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83381 q ha hb
  have h2 (q : Pattern) (ha : d33587 q = 1) (hb : d282284 q = 1) : d316242 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33587, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33587, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33588 q = 1) (hb : d282284 q = 1) : d316243 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33588, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33588, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33590 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33590, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83381 q ha hb
    | true =>
      simp only [d33590, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83423 q ha hb
  have h5 (q : Pattern) (ha : d33591 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33591, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33591, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33592 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33592, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33592, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33593 q = 1) (hb : d282284 q = 1) : d316244 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33593, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33593, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33348 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83381 q ha hb
    | true =>
      simp only [d33348, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
  have h9 (q : Pattern) (ha : d33349 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33350 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33227 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83361 q ha hb
    | true =>
      simp only [d33227, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h12 (q : Pattern) (ha : d33228 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33229 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33351 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33351, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33594 q = 1) (hb : d282284 q = 1) : d316245 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33594, d316245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33594, d316245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33595 q = 1) (hb : d282284 q = 1) : d316246 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33595, d316246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33595, d316246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro83425 (p : Pattern) (ha : d33601 p = 1) (hb : d282284 p = 1) : d316252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33596 q = 1) (hb : d282284 q = 1) : d316247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33596, d316247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83424 q ha hb
    | true =>
      simp only [d33596, d316247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33597 q = 1) (hb : d282284 q = 1) : d316248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33597, d316248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33597, d316248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33598 q = 1) (hb : d282284 q = 1) : d316249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33598, d316249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33598, d316249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33599 q = 1) (hb : d282284 q = 1) : d316250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33599, d316250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33599, d316250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33600 q = 1) (hb : d282284 q = 1) : d316251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33600, d316251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33600, d316251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33601 q = 1) (hb : d282284 q = 1) : d316252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33601, d316252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33601, d316252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83426 (p : Pattern) (ha : d33651 p = 1) (hb : d282284 p = 1) : d286017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33648 q = 1) (hb : d282284 q = 1) : d286014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33648, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33648, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33649 q = 1) (hb : d282284 q = 1) : d286015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33649, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33649, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33650 q = 1) (hb : d282284 q = 1) : d286016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33650, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33650, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33651 q = 1) (hb : d282284 q = 1) : d286017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33651, d286017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33651, d286017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83427 (p : Pattern) (ha : d265992 p = 1) (hb : d282284 p = 1) : d316258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33540 q = 1) (hb : d282284 q = 1) : d285968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33540, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83413 q ha hb
    | true =>
      simp only [d33540, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83414 q ha hb
  have h2 (q : Pattern) (ha : d33541 q = 1) (hb : d282284 q = 1) : d285969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33541, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33541, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33542 q = 1) (hb : d282284 q = 1) : d285970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33542, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33542, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33543 q = 1) (hb : d282284 q = 1) : d285971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33543, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33543, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33550 q = 1) (hb : d282284 q = 1) : d285975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33550, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83415 q ha hb
    | true =>
      simp only [d33550, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83416 q ha hb
  have h6 (q : Pattern) (ha : d33551 q = 1) (hb : d282284 q = 1) : d285976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33551, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33551, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33552 q = 1) (hb : d282284 q = 1) : d285977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33552, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33552, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33602 q = 1) (hb : d282284 q = 1) : d316253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33602, d316253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83425 q ha hb
    | true =>
      simp only [d33602, d316253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83401 q ha hb
  have h9 (q : Pattern) (ha : d265988 q = 1) (hb : d282284 q = 1) : d316254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d316254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265988, d316254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33652 q = 1) (hb : d282284 q = 1) : d286018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33652, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83426 q ha hb
    | true =>
      simp only [d33652, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33653 q = 1) (hb : d282284 q = 1) : d286019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33653, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33653, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265989 q = 1) (hb : d282284 q = 1) : d316255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d316255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265989, d316255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265990 q = 1) (hb : d282284 q = 1) : d316256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d316256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265990, d316256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265991 q = 1) (hb : d282284 q = 1) : d316257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d316257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265991, d316257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265992 q = 1) (hb : d282284 q = 1) : d316258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d316258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d316258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83428 (p : Pattern) (ha : d33658 p = 1) (hb : d282284 p = 1) : d286024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33536 q = 1) (hb : d282284 q = 1) : d285966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33536, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33536, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33658 q = 1) (hb : d282284 q = 1) : d286024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33658, d286024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33658, d286024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83429 (p : Pattern) (ha : d33659 p = 1) (hb : d282284 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33538 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33538, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33538, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33659 q = 1) (hb : d282284 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33659, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33659, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83430 (p : Pattern) (ha : d33664 p = 1) (hb : d282284 p = 1) : d286029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33544 q = 1) (hb : d282284 q = 1) : d285972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33544, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33544, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33545 q = 1) (hb : d282284 q = 1) : d285973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33545, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33545, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33664 q = 1) (hb : d282284 q = 1) : d286029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33664, d286029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33664, d286029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83431 (p : Pattern) (ha : d33665 p = 1) (hb : d282284 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83400 q ha hb
    | true =>
      simp only [d33507, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33547 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33547, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33547, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33548 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33548, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33548, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33665 q = 1) (hb : d282284 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33665, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33665, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83432 (p : Pattern) (ha : d33669 p = 1) (hb : d282284 p = 1) : d316259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33596 q = 1) (hb : d282284 q = 1) : d316247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33596, d316247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83424 q ha hb
    | true =>
      simp only [d33596, d316247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33597 q = 1) (hb : d282284 q = 1) : d316248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33597, d316248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33597, d316248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33598 q = 1) (hb : d282284 q = 1) : d316249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33598, d316249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33598, d316249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33599 q = 1) (hb : d282284 q = 1) : d316250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33599, d316250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33599, d316250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33600 q = 1) (hb : d282284 q = 1) : d316251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33600, d316251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33600, d316251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33669 q = 1) (hb : d282284 q = 1) : d316259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33669, d316259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33669, d316259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83433 (p : Pattern) (ha : d33675 p = 1) (hb : d282284 p = 1) : d286036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83399 q ha hb
    | true =>
      simp only [d33503, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33648 q = 1) (hb : d282284 q = 1) : d286014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33648, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33648, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33649 q = 1) (hb : d282284 q = 1) : d286015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33649, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33649, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33650 q = 1) (hb : d282284 q = 1) : d286016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33650, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33650, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33675 q = 1) (hb : d282284 q = 1) : d286036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33675, d286036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33675, d286036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83434 (p : Pattern) (ha : d265997 p = 1) (hb : d282284 p = 1) : d316265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33540 q = 1) (hb : d282284 q = 1) : d285968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33540, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83413 q ha hb
    | true =>
      simp only [d33540, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83414 q ha hb
  have h2 (q : Pattern) (ha : d33541 q = 1) (hb : d282284 q = 1) : d285969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33541, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33541, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33542 q = 1) (hb : d282284 q = 1) : d285970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33542, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33542, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33543 q = 1) (hb : d282284 q = 1) : d285971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33543, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33543, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33550 q = 1) (hb : d282284 q = 1) : d285975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33550, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83415 q ha hb
    | true =>
      simp only [d33550, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83416 q ha hb
  have h6 (q : Pattern) (ha : d33551 q = 1) (hb : d282284 q = 1) : d285976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33551, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33551, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33552 q = 1) (hb : d282284 q = 1) : d285977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33552, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33552, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33602 q = 1) (hb : d282284 q = 1) : d316253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33602, d316253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83425 q ha hb
    | true =>
      simp only [d33602, d316253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83401 q ha hb
  have h9 (q : Pattern) (ha : d265988 q = 1) (hb : d282284 q = 1) : d316254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d316254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265988, d316254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33652 q = 1) (hb : d282284 q = 1) : d286018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33652, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83426 q ha hb
    | true =>
      simp only [d33652, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33653 q = 1) (hb : d282284 q = 1) : d286019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33653, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33653, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d265989 q = 1) (hb : d282284 q = 1) : d316255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d316255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265989, d316255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265990 q = 1) (hb : d282284 q = 1) : d316256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d316256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265990, d316256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265991 q = 1) (hb : d282284 q = 1) : d316257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d316257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265991, d316257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33660 q = 1) (hb : d282284 q = 1) : d286025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33660, d286025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83428 q ha hb
    | true =>
      simp only [d33660, d286025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83429 q ha hb
  have h16 (q : Pattern) (ha : d33661 q = 1) (hb : d282284 q = 1) : d286026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33661, d286026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33661, d286026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33662 q = 1) (hb : d282284 q = 1) : d286027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33662, d286027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33662, d286027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33663 q = 1) (hb : d282284 q = 1) : d286028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33663, d286028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33663, d286028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33666 q = 1) (hb : d282284 q = 1) : d286030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33666, d286030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83430 q ha hb
    | true =>
      simp only [d33666, d286030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83431 q ha hb
  have h20 (q : Pattern) (ha : d33667 q = 1) (hb : d282284 q = 1) : d286031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33667, d286031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33667, d286031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d33668 q = 1) (hb : d282284 q = 1) : d286032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33668, d286032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33668, d286032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33670 q = 1) (hb : d282284 q = 1) : d316260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33670, d316260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83432 q ha hb
    | true =>
      simp only [d33670, d316260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83404 q ha hb
  have h23 (q : Pattern) (ha : d265993 q = 1) (hb : d282284 q = 1) : d316261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d316261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265993, d316261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33676 q = 1) (hb : d282284 q = 1) : d286037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33676, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83433 q ha hb
    | true =>
      simp only [d33676, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d33677 q = 1) (hb : d282284 q = 1) : d286038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33677, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33677, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d265994 q = 1) (hb : d282284 q = 1) : d316262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d316262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d265994, d316262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d265995 q = 1) (hb : d282284 q = 1) : d316263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d316263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265995, d316263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d265996 q = 1) (hb : d282284 q = 1) : d316264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d316264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265996, d316264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d265997 q = 1) (hb : d282284 q = 1) : d316265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d316265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265997, d316265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro83435 (p : Pattern) (ha : d266004 p = 1) (hb : d282284 p = 1) : d316272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33670 q = 1) (hb : d282284 q = 1) : d316260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33670, d316260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83432 q ha hb
    | true =>
      simp only [d33670, d316260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83404 q ha hb
  have h2 (q : Pattern) (ha : d265993 q = 1) (hb : d282284 q = 1) : d316261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d316261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265993, d316261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33676 q = 1) (hb : d282284 q = 1) : d286037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33676, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83433 q ha hb
    | true =>
      simp only [d33676, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33677 q = 1) (hb : d282284 q = 1) : d286038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33677, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33677, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d282284 q = 1) : d316262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d316262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265994, d316262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d282284 q = 1) : d316270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d316270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d316270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d282284 q = 1) : d316271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d316271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d316271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d282284 q = 1) : d316272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d316272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d316272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83436 (p : Pattern) (ha : d33723 p = 1) (hb : d282284 p = 1) : d316283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33709 q = 1) (hb : d282284 q = 1) : d316278 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33709, d316278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33709, d316278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
  have h2 (q : Pattern) (ha : d33567 q = 1) (hb : d282284 q = 1) : d316235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
    | true =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33710 q = 1) (hb : d282284 q = 1) : d316279 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33710, d316279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33710, d316279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33568 q = 1) (hb : d282284 q = 1) : d316236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33711 q = 1) (hb : d282284 q = 1) : d316280 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33711, d316280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33711, d316280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33712 q = 1) (hb : d282284 q = 1) : d316281 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33712, d316281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33712, d316281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33713 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33713, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33713, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
  have h8 (q : Pattern) (ha : d33572 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
    | true =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33714 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33714, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33714, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33573 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33715 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33715, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33715, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33716 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33716, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33716, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33717 q = 1) (hb : d282284 q = 1) : d316282 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33717, d316282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33717, d316282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33718 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
  have h15 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33719 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33720 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33721 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33439 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
  have h21 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33440 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33441 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33442 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33722 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33722, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33722, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d33723 q = 1) (hb : d282284 q = 1) : d316283 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33723, d316283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33723, d316283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro83437 (p : Pattern) (ha : d33727 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33439 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
  have h2 (q : Pattern) (ha : d33342 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83380 q ha hb
    | true =>
      simp only [d33342, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33440 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33440, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33343 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33343, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33441 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33441, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33442 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33442, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33443 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33443, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33727 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33727, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33727, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83438 (p : Pattern) (ha : d33733 p = 1) (hb : d282284 p = 1) : d316289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33724 q = 1) (hb : d282284 q = 1) : d316284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33724, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83436 q ha hb
    | true =>
      simp only [d33724, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83392 q ha hb
  have h2 (q : Pattern) (ha : d33725 q = 1) (hb : d282284 q = 1) : d316285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33725, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33725, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33726 q = 1) (hb : d282284 q = 1) : d316286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33726, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33726, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33728 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33728, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83392 q ha hb
    | true =>
      simp only [d33728, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83437 q ha hb
  have h5 (q : Pattern) (ha : d33729 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33729, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33729, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33730 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33730, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33730, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33731 q = 1) (hb : d282284 q = 1) : d316287 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33731, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33731, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33445 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83392 q ha hb
    | true =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
  have h9 (q : Pattern) (ha : d33446 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33447 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33270 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
    | true =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h12 (q : Pattern) (ha : d33271 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33272 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33448 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33732 q = 1) (hb : d282284 q = 1) : d316288 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33732, d316288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33732, d316288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33733 q = 1) (hb : d282284 q = 1) : d316289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33733, d316289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33733, d316289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro83439 (p : Pattern) (ha : d33738 p = 1) (hb : d282284 p = 1) : d285926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83392 q ha hb
    | true =>
      simp only [d33445, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33270 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83368 q ha hb
    | true =>
      simp only [d33270, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h5 (q : Pattern) (ha : d33271 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33272 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33448 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33736 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33736, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33736, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33737 q = 1) (hb : d282284 q = 1) : d285925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33737, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33737, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33738 q = 1) (hb : d282284 q = 1) : d285926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33738, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33738, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83440 (p : Pattern) (ha : d33744 p = 1) (hb : d282284 p = 1) : d316295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33734 q = 1) (hb : d282284 q = 1) : d316290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33734, d316290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83438 q ha hb
    | true =>
      simp only [d33734, d316290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33735 q = 1) (hb : d282284 q = 1) : d316291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33735, d316291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33735, d316291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33739 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83439 q ha hb
    | true =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33740 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33741 q = 1) (hb : d282284 q = 1) : d316292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33741, d316292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33741, d316292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33742 q = 1) (hb : d282284 q = 1) : d316293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33742, d316293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33742, d316293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33743 q = 1) (hb : d282284 q = 1) : d316294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33743, d316294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33743, d316294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33744 q = 1) (hb : d282284 q = 1) : d316295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33744, d316295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33744, d316295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83441 (p : Pattern) (ha : d33752 p = 1) (hb : d282284 p = 1) : d285932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33739 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83439 q ha hb
    | true =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33740 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33747 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33747, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83410 q ha hb
    | true =>
      simp only [d33747, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33748 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33748, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33748, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33749 q = 1) (hb : d282284 q = 1) : d285929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33749, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33749, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33750 q = 1) (hb : d282284 q = 1) : d285930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33750, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33750, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33751 q = 1) (hb : d282284 q = 1) : d285931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33751, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33751, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33752 q = 1) (hb : d282284 q = 1) : d285932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33752, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33752, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83442 (p : Pattern) (ha : d33791 p = 1) (hb : d282284 p = 1) : d286085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33739 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83439 q ha hb
    | true =>
      simp only [d33739, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33740 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33740, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33788 q = 1) (hb : d282284 q = 1) : d286082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33788, d286082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33788, d286082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33789 q = 1) (hb : d282284 q = 1) : d286083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33789, d286083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33789, d286083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33790 q = 1) (hb : d282284 q = 1) : d286084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33790, d286084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33790, d286084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33791 q = 1) (hb : d282284 q = 1) : d286085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33791, d286085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33791, d286085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83443 (p : Pattern) (ha : d266014 p = 1) (hb : d282284 p = 1) : d316301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33753 q = 1) (hb : d282284 q = 1) : d316296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33753, d316296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83440 q ha hb
    | true =>
      simp only [d33753, d316296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83441 q ha hb
  have h2 (q : Pattern) (ha : d266010 q = 1) (hb : d282284 q = 1) : d316297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d316297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266010, d316297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33792 q = 1) (hb : d282284 q = 1) : d286086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33792, d286086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83442 q ha hb
    | true =>
      simp only [d33792, d286086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33793 q = 1) (hb : d282284 q = 1) : d286087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33793, d286087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33793, d286087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d282284 q = 1) : d316298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d316298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266011, d316298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d282284 q = 1) : d316299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d316299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d316299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d282284 q = 1) : d316300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d316300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d316300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d282284 q = 1) : d316301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d316301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d316301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83444 (p : Pattern) (ha : d266020 p = 1) (hb : d282284 p = 1) : d316307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33523 q = 1) (hb : d282284 q = 1) : d285956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33523, d285956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33523, d285956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83403 q ha hb
  have h2 (q : Pattern) (ha : d33524 q = 1) (hb : d282284 q = 1) : d285957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33524, d285957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33524, d285957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33533 q = 1) (hb : d282284 q = 1) : d285963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33533, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83403 q ha hb
    | true =>
      simp only [d33533, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83406 q ha hb
  have h4 (q : Pattern) (ha : d33534 q = 1) (hb : d282284 q = 1) : d285964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33534, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33534, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33535 q = 1) (hb : d282284 q = 1) : d285965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33535, d285965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33535, d285965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265998 q = 1) (hb : d282284 q = 1) : d316266 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d316266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83427 q ha hb
    | true =>
      simp only [d265998, d316266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83434 q ha hb
  have h7 (q : Pattern) (ha : d33695 q = 1) (hb : d282284 q = 1) : d286045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33695, d286045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83407 q ha hb
    | true =>
      simp only [d33695, d286045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83408 q ha hb
  have h8 (q : Pattern) (ha : d265999 q = 1) (hb : d282284 q = 1) : d316267 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d316267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265999, d316267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266000 q = 1) (hb : d282284 q = 1) : d316268 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d316268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266000, d316268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d266001 q = 1) (hb : d282284 q = 1) : d316269 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d316269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266001, d316269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266005 q = 1) (hb : d282284 q = 1) : d316273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d316273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266005, d316273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83435 q ha hb
  have h12 (q : Pattern) (ha : d33704 q = 1) (hb : d282284 q = 1) : d257491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33704, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33704, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83409 q ha hb
  have h13 (q : Pattern) (ha : d266006 q = 1) (hb : d282284 q = 1) : d316274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d316274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d266006, d316274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266007 q = 1) (hb : d282284 q = 1) : d316275 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d316275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266007, d316275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d266008 q = 1) (hb : d282284 q = 1) : d316276 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d316276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266008, d316276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d266009 q = 1) (hb : d282284 q = 1) : d316277 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d316277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266009, d316277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266015 q = 1) (hb : d282284 q = 1) : d316302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d316302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266015, d316302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83443 q ha hb
  have h18 (q : Pattern) (ha : d33809 q = 1) (hb : d282284 q = 1) : d257537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33809, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33809, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83412 q ha hb
  have h19 (q : Pattern) (ha : d266016 q = 1) (hb : d282284 q = 1) : d316303 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d316303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266016, d316303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d266017 q = 1) (hb : d282284 q = 1) : d316304 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d316304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d266017, d316304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d266018 q = 1) (hb : d282284 q = 1) : d316305 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d316305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d266018, d316305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d266019 q = 1) (hb : d282284 q = 1) : d316306 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d316306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266019, d316306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d266020 q = 1) (hb : d282284 q = 1) : d316307 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d316307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266020, d316307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro83445 (p : Pattern) (ha : d266026 p = 1) (hb : d282284 p = 1) : d316313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d282284 q = 1) : d316308 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d316308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d316308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83444 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d282284 q = 1) : d316309 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d316309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d316309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d282284 q = 1) : d316310 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d316310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d316310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d282284 q = 1) : d316311 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d316311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d316311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d282284 q = 1) : d316312 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d316312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d316312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d282284 q = 1) : d316313 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d316313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d316313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83446 (p : Pattern) (ha : d33822 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33217 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33217, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d33218 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33218, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33219 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33219, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d33822 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33822, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33822, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h10 p ha hb
theorem andIntro83447 (p : Pattern) (ha : d33828 p = 1) (hb : d282284 p = 1) : d316240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33567 q = 1) (hb : d282284 q = 1) : d316235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
    | true =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33568 q = 1) (hb : d282284 q = 1) : d316236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33569 q = 1) (hb : d282284 q = 1) : d316237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33569, d316237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33569, d316237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33570 q = 1) (hb : d282284 q = 1) : d316238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33570, d316238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33570, d316238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33572 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
    | true =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33573 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33574 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33574, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33574, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33575 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33575, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33575, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33576 q = 1) (hb : d282284 q = 1) : d316239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33576, d316239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33576, d316239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33582 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33583 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33825 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33826 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33827 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33827, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33827, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33828 q = 1) (hb : d282284 q = 1) : d316240 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33828, d316240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33828, d316240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83448 (p : Pattern) (ha : d33831 p = 1) (hb : d282284 p = 1) : d285877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
    | true =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33825 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33826 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33829 q = 1) (hb : d282284 q = 1) : d285876 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33829, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33829, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33830 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33831 q = 1) (hb : d282284 q = 1) : d285877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33831, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33831, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83449 (p : Pattern) (ha : d33835 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33825 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33826 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33830 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33835 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33835, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33835, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83450 (p : Pattern) (ha : d33842 p = 1) (hb : d282284 p = 1) : d316316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33832 q = 1) (hb : d282284 q = 1) : d316241 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33832, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83447 q ha hb
    | true =>
      simp only [d33832, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83448 q ha hb
  have h2 (q : Pattern) (ha : d33833 q = 1) (hb : d282284 q = 1) : d316242 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33833, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33833, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33834 q = 1) (hb : d282284 q = 1) : d316243 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33834, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33834, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33836 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83448 q ha hb
    | true =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83449 q ha hb
  have h5 (q : Pattern) (ha : d33837 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33838 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33839 q = 1) (hb : d282284 q = 1) : d316244 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33839, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33839, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33840 q = 1) (hb : d282284 q = 1) : d286105 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33840, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33840, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33841 q = 1) (hb : d282284 q = 1) : d316315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33841, d316315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33841, d316315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33842 q = 1) (hb : d282284 q = 1) : d316316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33842, d316316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33842, d316316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83451 (p : Pattern) (ha : d33846 p = 1) (hb : d282284 p = 1) : d286111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33836 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83448 q ha hb
    | true =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83449 q ha hb
  have h2 (q : Pattern) (ha : d33837 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33838 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33840 q = 1) (hb : d282284 q = 1) : d286105 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33840, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33840, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33845 q = 1) (hb : d282284 q = 1) : d286110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33845, d286110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33845, d286110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33846 q = 1) (hb : d282284 q = 1) : d286111 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33846, d286111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33846, d286111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83452 (p : Pattern) (ha : d33852 p = 1) (hb : d282284 p = 1) : d316322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d282284 q = 1) : d316320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33851 q = 1) (hb : d282284 q = 1) : d316321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33851, d316321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33851, d316321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33852 q = 1) (hb : d282284 q = 1) : d316322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33852, d316322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33852, d316322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83453 (p : Pattern) (ha : d33856 p = 1) (hb : d282284 p = 1) : d286121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33855 q = 1) (hb : d282284 q = 1) : d286120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33855, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33855, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33856 q = 1) (hb : d282284 q = 1) : d286121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33856, d286121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33856, d286121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83454 (p : Pattern) (ha : d33862 p = 1) (hb : d282284 p = 1) : d316328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d282284 q = 1) : d316323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83452 q ha hb
    | true =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83453 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d282284 q = 1) : d316324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d282284 q = 1) : d316325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d282284 q = 1) : d316326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d282284 q = 1) : d316327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33862 q = 1) (hb : d282284 q = 1) : d316328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33862, d316328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33862, d316328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83455 (p : Pattern) (ha : d33865 p = 1) (hb : d282284 p = 1) : d316331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d282284 q = 1) : d316320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33851 q = 1) (hb : d282284 q = 1) : d316321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33851, d316321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33851, d316321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33865 q = 1) (hb : d282284 q = 1) : d316331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33865, d316331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33865, d316331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83456 (p : Pattern) (ha : d33866 p = 1) (hb : d282284 p = 1) : d286131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33855 q = 1) (hb : d282284 q = 1) : d286120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33855, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33855, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33866 q = 1) (hb : d282284 q = 1) : d286131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33866, d286131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33866, d286131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83457 (p : Pattern) (ha : d33872 p = 1) (hb : d282284 p = 1) : d316337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d282284 q = 1) : d316323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83452 q ha hb
    | true =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83453 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d282284 q = 1) : d316324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d282284 q = 1) : d316325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d282284 q = 1) : d316326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d282284 q = 1) : d316327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33867 q = 1) (hb : d282284 q = 1) : d316332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33867, d316332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83455 q ha hb
    | true =>
      simp only [d33867, d316332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83456 q ha hb
  have h7 (q : Pattern) (ha : d33868 q = 1) (hb : d282284 q = 1) : d316333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33868, d316333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33868, d316333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33869 q = 1) (hb : d282284 q = 1) : d316334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33869, d316334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33869, d316334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33870 q = 1) (hb : d282284 q = 1) : d316335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33870, d316335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33870, d316335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33871 q = 1) (hb : d282284 q = 1) : d316336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33871, d316336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33871, d316336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33872 q = 1) (hb : d282284 q = 1) : d316337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33872, d316337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33872, d316337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83458 (p : Pattern) (ha : d34058 p = 1) (hb : d282284 p = 1) : d316430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33857 q = 1) (hb : d282284 q = 1) : d316323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83452 q ha hb
    | true =>
      simp only [d33857, d316323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83453 q ha hb
  have h2 (q : Pattern) (ha : d33858 q = 1) (hb : d282284 q = 1) : d316324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33858, d316324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33859 q = 1) (hb : d282284 q = 1) : d316325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33859, d316325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33860 q = 1) (hb : d282284 q = 1) : d316326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33860, d316326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33861 q = 1) (hb : d282284 q = 1) : d316327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33861, d316327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34053 q = 1) (hb : d282284 q = 1) : d286235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34053, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83453 q ha hb
    | true =>
      simp only [d34053, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34054 q = 1) (hb : d282284 q = 1) : d286236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34054, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34054, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34055 q = 1) (hb : d282284 q = 1) : d286237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34055, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34055, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34056 q = 1) (hb : d282284 q = 1) : d286238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34056, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34056, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34057 q = 1) (hb : d282284 q = 1) : d286239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34057, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34057, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34058 q = 1) (hb : d282284 q = 1) : d316430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34058, d316430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34058, d316430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83459 (p : Pattern) (ha : d34064 p = 1) (hb : d282284 p = 1) : d286246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34053 q = 1) (hb : d282284 q = 1) : d286235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34053, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83453 q ha hb
    | true =>
      simp only [d34053, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34054 q = 1) (hb : d282284 q = 1) : d286236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34054, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34054, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34055 q = 1) (hb : d282284 q = 1) : d286237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34055, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34055, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34056 q = 1) (hb : d282284 q = 1) : d286238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34056, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34056, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34057 q = 1) (hb : d282284 q = 1) : d286239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34057, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34057, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34059 q = 1) (hb : d282284 q = 1) : d286241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34059, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83456 q ha hb
    | true =>
      simp only [d34059, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34060 q = 1) (hb : d282284 q = 1) : d286242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34060, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34060, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34061 q = 1) (hb : d282284 q = 1) : d286243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34061, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34061, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34062 q = 1) (hb : d282284 q = 1) : d286244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34062, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34062, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34063 q = 1) (hb : d282284 q = 1) : d286245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34063, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34063, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34064 q = 1) (hb : d282284 q = 1) : d286246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34064, d286246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34064, d286246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83460 (p : Pattern) (ha : d34073 p = 1) (hb : d282284 p = 1) : d286255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34059 q = 1) (hb : d282284 q = 1) : d286241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34059, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83456 q ha hb
    | true =>
      simp only [d34059, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34060 q = 1) (hb : d282284 q = 1) : d286242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34060, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34060, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34061 q = 1) (hb : d282284 q = 1) : d286243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34061, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34061, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34062 q = 1) (hb : d282284 q = 1) : d286244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34062, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34062, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34063 q = 1) (hb : d282284 q = 1) : d286245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34063, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34063, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34073 q = 1) (hb : d282284 q = 1) : d286255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34073, d286255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34073, d286255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83461 (p : Pattern) (ha : d34110 p = 1) (hb : d282284 p = 1) : d285920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83379 q ha hb
    | true =>
      simp only [d33334, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34094 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
  have h8 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34095 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34096 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34097 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34109 q = 1) (hb : d282284 q = 1) : d285919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34109, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34109, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34103 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d34110 q = 1) (hb : d282284 q = 1) : d285920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34110, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34110, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83462 (p : Pattern) (ha : d34114 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34094 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
  have h2 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34095 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34096 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34097 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34103 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34114 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34114, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34114, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83463 (p : Pattern) (ha : d34133 p = 1) (hb : d282284 p = 1) : d286298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34115 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83461 q ha hb
    | true =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83462 q ha hb
  have h2 (q : Pattern) (ha : d34116 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34117 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34123 q = 1) (hb : d282284 q = 1) : d286288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34123, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34123, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34132 q = 1) (hb : d282284 q = 1) : d286297 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34132, d286297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34132, d286297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34133 q = 1) (hb : d282284 q = 1) : d286298 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34133, d286298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34133, d286298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83464 (p : Pattern) (ha : d34204 p = 1) (hb : d282284 p = 1) : d286321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34134 q = 1) (hb : d282284 q = 1) : d286299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34134, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83463 q ha hb
    | true =>
      simp only [d34134, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34135 q = 1) (hb : d282284 q = 1) : d286300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34135, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34135, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34201 q = 1) (hb : d282284 q = 1) : d286318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34201, d286318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34201, d286318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34202 q = 1) (hb : d282284 q = 1) : d286319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34202, d286319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34202, d286319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34203 q = 1) (hb : d282284 q = 1) : d286320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34203, d286320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34203, d286320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34204 q = 1) (hb : d282284 q = 1) : d286321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34204, d286321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34204, d286321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83465 (p : Pattern) (ha : d34210 p = 1) (hb : d282284 p = 1) : d286327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34205 q = 1) (hb : d282284 q = 1) : d286322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34205, d286322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83464 q ha hb
    | true =>
      simp only [d34205, d286322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34206 q = 1) (hb : d282284 q = 1) : d286323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34206, d286323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34206, d286323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34207 q = 1) (hb : d282284 q = 1) : d286324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34207, d286324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34207, d286324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34208 q = 1) (hb : d282284 q = 1) : d286325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34208, d286325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34208, d286325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34209 q = 1) (hb : d282284 q = 1) : d286326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34209, d286326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34209, d286326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34210 q = 1) (hb : d282284 q = 1) : d286327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d34210, d286327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34210, d286327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83466 (p : Pattern) (ha : d33877 p = 1) (hb : d282284 p = 1) : d316342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d282284 q = 1) : d316320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33876 q = 1) (hb : d282284 q = 1) : d316341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33876, d316341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33876, d316341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33877 q = 1) (hb : d282284 q = 1) : d316342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33877, d316342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33877, d316342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83467 (p : Pattern) (ha : d33879 p = 1) (hb : d282284 p = 1) : d286144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33878 q = 1) (hb : d282284 q = 1) : d286143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33878, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33878, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33879 q = 1) (hb : d282284 q = 1) : d286144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33879, d286144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33879, d286144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83468 (p : Pattern) (ha : d33886 p = 1) (hb : d282284 p = 1) : d316349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33884 q = 1) (hb : d282284 q = 1) : d316347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33884, d316347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33884, d316347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33885 q = 1) (hb : d282284 q = 1) : d316348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33885, d316348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33885, d316348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33886 q = 1) (hb : d282284 q = 1) : d316349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33886, d316349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33886, d316349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83469 (p : Pattern) (ha : d33889 p = 1) (hb : d282284 p = 1) : d286154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33887 q = 1) (hb : d282284 q = 1) : d286152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33887, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33887, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33888 q = 1) (hb : d282284 q = 1) : d286153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33888, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33888, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33889 q = 1) (hb : d282284 q = 1) : d286154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33889, d286154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33889, d286154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83470 (p : Pattern) (ha : d33894 p = 1) (hb : d282283 p = 1) : d34352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33553 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5121 q = 1) (hb : d261984 q = 1) : d5121 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33894 q = 1) (hb : d282283 q = 1) : d34352 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33894, d282283, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33894, d282283, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83471 (p : Pattern) (ha : d33897 p = 1) (hb : d282283 p = 1) : d316228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33554 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33559 q = 1) (hb : d261984 q = 1) : d33559 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33897 q = 1) (hb : d282283 q = 1) : d316228 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33897, d282283, d316228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33897, d282283, d316228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83472 (p : Pattern) (ha : d33906 p = 1) (hb : d282284 p = 1) : d316357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33556 q = 1) (hb : d282284 q = 1) : d286612 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83417 q ha hb
    | true =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33557 q = 1) (hb : d282284 q = 1) : d286613 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33893 q = 1) (hb : d282284 q = 1) : d316353 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33893, d316353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33893, d316353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33895 q = 1) (hb : d282284 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33895, d282284, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83470 q ha hb
    | true =>
      simp only [d33895, d282284, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d33896 q = 1) (hb : d282284 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33896, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33896, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33898 q = 1) (hb : d282284 q = 1) : d316229 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33898, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83471 q ha hb
    | true =>
      simp only [d33898, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d33899 q = 1) (hb : d282284 q = 1) : d316230 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33899, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33899, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33900 q = 1) (hb : d282284 q = 1) : d316354 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33900, d316354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33900, d316354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33901 q = 1) (hb : d282284 q = 1) : d316355 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33901, d316355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33901, d316355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33902 q = 1) (hb : d282284 q = 1) : d316356 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33902, d316356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33902, d316356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33558 q = 1) (hb : d282284 q = 1) : d316227 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d33903 q = 1) (hb : d282284 q = 1) : d316231 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33903, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33903, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d33904 q = 1) (hb : d282284 q = 1) : d316232 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33904, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33904, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33905 q = 1) (hb : d282284 q = 1) : d316233 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33905, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33905, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33906 q = 1) (hb : d282284 q = 1) : d316357 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33906, d316357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33906, d316357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro83473 (p : Pattern) (ha : d33911 p = 1) (hb : d282283 p = 1) : d258089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1541 q = 1) (hb : d261984 q = 1) : d1541 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33911 q = 1) (hb : d282283 q = 1) : d258089 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33911, d282283, d258089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d33911, d282283, d258089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro83474 (p : Pattern) (ha : d33917 p = 1) (hb : d282284 p = 1) : d316367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d282284 q = 1) : d286612 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83417 q ha hb
    | true =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33557 q = 1) (hb : d282284 q = 1) : d286613 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33328 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83378 q ha hb
    | true =>
      simp only [d33328, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33329 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33329, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33558 q = 1) (hb : d282284 q = 1) : d316227 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33558, d316227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33561 q = 1) (hb : d282284 q = 1) : d316229 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33561, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83418 q ha hb
    | true =>
      simp only [d33561, d282284, d316229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33562 q = 1) (hb : d282284 q = 1) : d316230 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33562, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33562, d316230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d33563 q = 1) (hb : d282284 q = 1) : d316231 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33563, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33563, d316231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33564 q = 1) (hb : d282284 q = 1) : d316232 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33564, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33564, d316232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33565 q = 1) (hb : d282284 q = 1) : d316233 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33565, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33565, d316233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d33912 q = 1) (hb : d282284 q = 1) : d316362 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33912, d282284, d316362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83473 q ha hb
    | true =>
      simp only [d33912, d282284, d316362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33913 q = 1) (hb : d282284 q = 1) : d316363 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33913, d316363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33913, d316363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d33914 q = 1) (hb : d282284 q = 1) : d316364 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33914, d316364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33914, d316364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d33915 q = 1) (hb : d282284 q = 1) : d316365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33915, d316365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33915, d316365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d33916 q = 1) (hb : d282284 q = 1) : d316366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33916, d316366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d33916, d316366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d33917 q = 1) (hb : d282284 q = 1) : d316367 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33917, d316367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33917, d316367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83475 (p : Pattern) (ha : d33926 p = 1) (hb : d282284 p = 1) : d316376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d282284 q = 1) : d286612 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83417 q ha hb
    | true =>
      simp only [d33556, d282284, d286612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33557 q = 1) (hb : d282284 q = 1) : d286613 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, d286613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33912 q = 1) (hb : d282284 q = 1) : d316362 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33912, d282284, d316362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83473 q ha hb
    | true =>
      simp only [d33912, d282284, d316362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33913 q = 1) (hb : d282284 q = 1) : d316363 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33913, d316363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33913, d316363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d33923 q = 1) (hb : d282284 q = 1) : d316373 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33923, d316373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33923, d316373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33924 q = 1) (hb : d282284 q = 1) : d316374 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33924, d316374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33924, d316374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d33925 q = 1) (hb : d282284 q = 1) : d316375 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33925, d316375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33925, d316375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33215 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83359 q ha hb
    | true =>
      simp only [d33215, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33216 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33216, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d33914 q = 1) (hb : d282284 q = 1) : d316364 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33914, d316364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33914, d316364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33915 q = 1) (hb : d282284 q = 1) : d316365 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33915, d316365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33915, d316365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d33916 q = 1) (hb : d282284 q = 1) : d316366 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33916, d316366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33916, d316366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d33926 q = 1) (hb : d282284 q = 1) : d316376 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33926, d316376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33926, d316376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro83476 (p : Pattern) (ha : d33932 p = 1) (hb : d282284 p = 1) : d316382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33907 q = 1) (hb : d282284 q = 1) : d316358 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33907, d316358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83472 q ha hb
    | true =>
      simp only [d33907, d316358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33908 q = 1) (hb : d282284 q = 1) : d316359 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33908, d316359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33908, d316359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33909 q = 1) (hb : d282284 q = 1) : d316360 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33909, d316360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33909, d316360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33910 q = 1) (hb : d282284 q = 1) : d316361 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33910, d316361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33910, d316361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33918 q = 1) (hb : d282284 q = 1) : d316368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33918, d316368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83474 q ha hb
    | true =>
      simp only [d33918, d316368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33919 q = 1) (hb : d282284 q = 1) : d316369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33919, d316369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33919, d316369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33920 q = 1) (hb : d282284 q = 1) : d316370 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33920, d316370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33920, d316370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33921 q = 1) (hb : d282284 q = 1) : d316371 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33921, d316371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33921, d316371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33922 q = 1) (hb : d282284 q = 1) : d316372 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33922, d316372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33922, d316372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33927 q = 1) (hb : d282284 q = 1) : d316377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33927, d316377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83475 q ha hb
    | true =>
      simp only [d33927, d316377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33928 q = 1) (hb : d282284 q = 1) : d316378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33928, d316378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33928, d316378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33929 q = 1) (hb : d282284 q = 1) : d316379 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33929, d316379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33929, d316379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33930 q = 1) (hb : d282284 q = 1) : d316380 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33930, d316380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33930, d316380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33582 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33583 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33931 q = 1) (hb : d282284 q = 1) : d316381 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33931, d316381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33931, d316381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33932 q = 1) (hb : d282284 q = 1) : d316382 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33932, d316382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33932, d316382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83477 (p : Pattern) (ha : d33936 p = 1) (hb : d282284 p = 1) : d286188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33582 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33583 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33583, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33825 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33825, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33826 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33826, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33827 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33827, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33827, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33830 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33830, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33936 q = 1) (hb : d282284 q = 1) : d286188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33936, d286188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33936, d286188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83478 (p : Pattern) (ha : d33942 p = 1) (hb : d282284 p = 1) : d316391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33933 q = 1) (hb : d282284 q = 1) : d316383 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33933, d316383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83476 q ha hb
    | true =>
      simp only [d33933, d316383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83447 q ha hb
  have h2 (q : Pattern) (ha : d33934 q = 1) (hb : d282284 q = 1) : d316384 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33934, d316384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33934, d316384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33935 q = 1) (hb : d282284 q = 1) : d316385 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33935, d316385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33935, d316385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33937 q = 1) (hb : d282284 q = 1) : d316386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33937, d316386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83447 q ha hb
    | true =>
      simp only [d33937, d316386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83477 q ha hb
  have h5 (q : Pattern) (ha : d33938 q = 1) (hb : d282284 q = 1) : d316387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33938, d316387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33938, d316387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33939 q = 1) (hb : d282284 q = 1) : d316388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33939, d316388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33939, d316388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33940 q = 1) (hb : d282284 q = 1) : d316389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33940, d316389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33940, d316389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33832 q = 1) (hb : d282284 q = 1) : d316241 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33832, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83447 q ha hb
    | true =>
      simp only [d33832, d316241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83448 q ha hb
  have h9 (q : Pattern) (ha : d33833 q = 1) (hb : d282284 q = 1) : d316242 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33833, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33833, d316242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33834 q = 1) (hb : d282284 q = 1) : d316243 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33834, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33834, d316243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33836 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83448 q ha hb
    | true =>
      simp only [d33836, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83449 q ha hb
  have h12 (q : Pattern) (ha : d33837 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33837, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33838 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33838, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33839 q = 1) (hb : d282284 q = 1) : d316244 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33839, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33839, d316244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33941 q = 1) (hb : d282284 q = 1) : d316390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33941, d316390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33941, d316390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33942 q = 1) (hb : d282284 q = 1) : d316391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33942, d316391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33942, d316391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro83479 (p : Pattern) (ha : d33948 p = 1) (hb : d282284 p = 1) : d316397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33943 q = 1) (hb : d282284 q = 1) : d316392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33943, d316392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83478 q ha hb
    | true =>
      simp only [d33943, d316392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33944 q = 1) (hb : d282284 q = 1) : d316393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33944, d316393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33944, d316393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33945 q = 1) (hb : d282284 q = 1) : d316394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33945, d316394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33945, d316394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33946 q = 1) (hb : d282284 q = 1) : d316395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33946, d316395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33946, d316395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33947 q = 1) (hb : d282284 q = 1) : d316396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33947, d316396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33947, d316396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33948 q = 1) (hb : d282284 q = 1) : d316397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33948, d316397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33948, d316397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83480 (p : Pattern) (ha : d34021 p = 1) (hb : d282284 p = 1) : d316403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34018 q = 1) (hb : d282284 q = 1) : d316400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34018, d316400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34018, d316400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34019 q = 1) (hb : d282284 q = 1) : d316401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34019, d316401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34019, d316401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34020 q = 1) (hb : d282284 q = 1) : d316402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34020, d316402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34020, d316402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34021 q = 1) (hb : d282284 q = 1) : d316403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34021, d316403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34021, d316403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83481 (p : Pattern) (ha : d266032 p = 1) (hb : d282284 p = 1) : d316409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33880 q = 1) (hb : d282284 q = 1) : d316343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33880, d316343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83466 q ha hb
    | true =>
      simp only [d33880, d316343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83467 q ha hb
  have h2 (q : Pattern) (ha : d33881 q = 1) (hb : d282284 q = 1) : d316344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33881, d316344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33881, d316344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33882 q = 1) (hb : d282284 q = 1) : d316345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33882, d316345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33882, d316345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33883 q = 1) (hb : d282284 q = 1) : d316346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33883, d316346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33883, d316346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33890 q = 1) (hb : d282284 q = 1) : d316350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33890, d316350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83468 q ha hb
    | true =>
      simp only [d33890, d316350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83469 q ha hb
  have h6 (q : Pattern) (ha : d33891 q = 1) (hb : d282284 q = 1) : d316351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33891, d316351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33891, d316351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33892 q = 1) (hb : d282284 q = 1) : d316352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33892, d316352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33892, d316352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33949 q = 1) (hb : d282284 q = 1) : d316398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33949, d316398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83479 q ha hb
    | true =>
      simp only [d33949, d316398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83452 q ha hb
  have h9 (q : Pattern) (ha : d266028 q = 1) (hb : d282284 q = 1) : d316399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d316399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266028, d316399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d34022 q = 1) (hb : d282284 q = 1) : d316404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34022, d316404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83480 q ha hb
    | true =>
      simp only [d34022, d316404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34023 q = 1) (hb : d282284 q = 1) : d316405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34023, d316405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34023, d316405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d266029 q = 1) (hb : d282284 q = 1) : d316406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d316406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266029, d316406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266030 q = 1) (hb : d282284 q = 1) : d316407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d316407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266030, d316407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266031 q = 1) (hb : d282284 q = 1) : d316408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d316408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266031, d316408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266032 q = 1) (hb : d282284 q = 1) : d316409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d316409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d316409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83482 (p : Pattern) (ha : d34028 p = 1) (hb : d282284 p = 1) : d316410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33850 q = 1) (hb : d282284 q = 1) : d316320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33850, d316320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33876 q = 1) (hb : d282284 q = 1) : d316341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33876, d316341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33876, d316341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34028 q = 1) (hb : d282284 q = 1) : d316410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34028, d316410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34028, d316410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83483 (p : Pattern) (ha : d34029 p = 1) (hb : d282284 p = 1) : d286214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33854 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33854, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33878 q = 1) (hb : d282284 q = 1) : d286143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33878, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33878, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34029 q = 1) (hb : d282284 q = 1) : d286214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34029, d286214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34029, d286214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83484 (p : Pattern) (ha : d34034 p = 1) (hb : d282284 p = 1) : d316415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33849 q = 1) (hb : d282284 q = 1) : d316319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33849, d316319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33884 q = 1) (hb : d282284 q = 1) : d316347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33884, d316347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33884, d316347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33885 q = 1) (hb : d282284 q = 1) : d316348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33885, d316348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33885, d316348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34034 q = 1) (hb : d282284 q = 1) : d316415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34034, d316415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34034, d316415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83485 (p : Pattern) (ha : d34035 p = 1) (hb : d282284 p = 1) : d286220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33847 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83451 q ha hb
    | true =>
      simp only [d33847, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33848 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33848, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33853 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33853, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33887 q = 1) (hb : d282284 q = 1) : d286152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33887, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33887, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33888 q = 1) (hb : d282284 q = 1) : d286153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33888, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33888, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34035 q = 1) (hb : d282284 q = 1) : d286220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34035, d286220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34035, d286220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83486 (p : Pattern) (ha : d34039 p = 1) (hb : d282284 p = 1) : d316419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33943 q = 1) (hb : d282284 q = 1) : d316392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33943, d316392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83478 q ha hb
    | true =>
      simp only [d33943, d316392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33944 q = 1) (hb : d282284 q = 1) : d316393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33944, d316393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33944, d316393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33945 q = 1) (hb : d282284 q = 1) : d316394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33945, d316394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33945, d316394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33946 q = 1) (hb : d282284 q = 1) : d316395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33946, d316395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33946, d316395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33947 q = 1) (hb : d282284 q = 1) : d316396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33947, d316396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33947, d316396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34039 q = 1) (hb : d282284 q = 1) : d316419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34039, d316419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34039, d316419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83487 (p : Pattern) (ha : d34045 p = 1) (hb : d282284 p = 1) : d316422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33843 q = 1) (hb : d282284 q = 1) : d316317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83450 q ha hb
    | true =>
      simp only [d33843, d316317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33844 q = 1) (hb : d282284 q = 1) : d316318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33844, d316318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34018 q = 1) (hb : d282284 q = 1) : d316400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34018, d316400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34018, d316400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34019 q = 1) (hb : d282284 q = 1) : d316401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34019, d316401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34019, d316401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34020 q = 1) (hb : d282284 q = 1) : d316402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34020, d316402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34020, d316402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34045 q = 1) (hb : d282284 q = 1) : d316422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34045, d316422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34045, d316422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83488 (p : Pattern) (ha : d266037 p = 1) (hb : d282284 p = 1) : d316428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33880 q = 1) (hb : d282284 q = 1) : d316343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33880, d316343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83466 q ha hb
    | true =>
      simp only [d33880, d316343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83467 q ha hb
  have h2 (q : Pattern) (ha : d33881 q = 1) (hb : d282284 q = 1) : d316344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33881, d316344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33881, d316344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33882 q = 1) (hb : d282284 q = 1) : d316345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33882, d316345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33882, d316345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33883 q = 1) (hb : d282284 q = 1) : d316346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33883, d316346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33883, d316346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33890 q = 1) (hb : d282284 q = 1) : d316350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33890, d316350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83468 q ha hb
    | true =>
      simp only [d33890, d316350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83469 q ha hb
  have h6 (q : Pattern) (ha : d33891 q = 1) (hb : d282284 q = 1) : d316351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33891, d316351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33891, d316351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33892 q = 1) (hb : d282284 q = 1) : d316352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33892, d316352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33892, d316352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33949 q = 1) (hb : d282284 q = 1) : d316398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33949, d316398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83479 q ha hb
    | true =>
      simp only [d33949, d316398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83452 q ha hb
  have h9 (q : Pattern) (ha : d266028 q = 1) (hb : d282284 q = 1) : d316399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d316399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266028, d316399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d34022 q = 1) (hb : d282284 q = 1) : d316404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34022, d316404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83480 q ha hb
    | true =>
      simp only [d34022, d316404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34023 q = 1) (hb : d282284 q = 1) : d316405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34023, d316405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34023, d316405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d266029 q = 1) (hb : d282284 q = 1) : d316406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d316406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266029, d316406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266030 q = 1) (hb : d282284 q = 1) : d316407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d316407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266030, d316407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266031 q = 1) (hb : d282284 q = 1) : d316408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d316408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266031, d316408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d34030 q = 1) (hb : d282284 q = 1) : d316411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34030, d316411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83482 q ha hb
    | true =>
      simp only [d34030, d316411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83483 q ha hb
  have h16 (q : Pattern) (ha : d34031 q = 1) (hb : d282284 q = 1) : d316412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34031, d316412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34031, d316412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d34032 q = 1) (hb : d282284 q = 1) : d316413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34032, d316413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d34032, d316413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d34033 q = 1) (hb : d282284 q = 1) : d316414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34033, d316414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34033, d316414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d34036 q = 1) (hb : d282284 q = 1) : d316416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34036, d316416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83484 q ha hb
    | true =>
      simp only [d34036, d316416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83485 q ha hb
  have h20 (q : Pattern) (ha : d34037 q = 1) (hb : d282284 q = 1) : d316417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34037, d316417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34037, d316417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d34038 q = 1) (hb : d282284 q = 1) : d316418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34038, d316418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d34038, d316418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d34040 q = 1) (hb : d282284 q = 1) : d316420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34040, d316420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83486 q ha hb
    | true =>
      simp only [d34040, d316420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83455 q ha hb
  have h23 (q : Pattern) (ha : d266033 q = 1) (hb : d282284 q = 1) : d316421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d316421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d266033, d316421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d34046 q = 1) (hb : d282284 q = 1) : d316423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34046, d316423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83487 q ha hb
    | true =>
      simp only [d34046, d316423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d34047 q = 1) (hb : d282284 q = 1) : d316424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34047, d316424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d34047, d316424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d266034 q = 1) (hb : d282284 q = 1) : d316425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d316425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d266034, d316425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d266035 q = 1) (hb : d282284 q = 1) : d316426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d316426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266035, d316426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d266036 q = 1) (hb : d282284 q = 1) : d316427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d316427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d266036, d316427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d266037 q = 1) (hb : d282284 q = 1) : d316428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d316428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266037, d316428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro83489 (p : Pattern) (ha : d266044 p = 1) (hb : d282284 p = 1) : d316437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34040 q = 1) (hb : d282284 q = 1) : d316420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34040, d316420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83486 q ha hb
    | true =>
      simp only [d34040, d316420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83455 q ha hb
  have h2 (q : Pattern) (ha : d266033 q = 1) (hb : d282284 q = 1) : d316421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d316421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266033, d316421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34046 q = 1) (hb : d282284 q = 1) : d316423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34046, d316423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83487 q ha hb
    | true =>
      simp only [d34046, d316423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34047 q = 1) (hb : d282284 q = 1) : d316424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34047, d316424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34047, d316424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d282284 q = 1) : d316425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d316425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266034, d316425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d282284 q = 1) : d316435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d316435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d316435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d282284 q = 1) : d316436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d316436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d316436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d282284 q = 1) : d316437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d316437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d316437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83490 (p : Pattern) (ha : d34093 p = 1) (hb : d282284 p = 1) : d316457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34079 q = 1) (hb : d282284 q = 1) : d316443 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34079, d316443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34079, d316443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83472 q ha hb
  have h2 (q : Pattern) (ha : d33907 q = 1) (hb : d282284 q = 1) : d316358 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33907, d316358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83472 q ha hb
    | true =>
      simp only [d33907, d316358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34080 q = 1) (hb : d282284 q = 1) : d316444 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34080, d316444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34080, d316444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33908 q = 1) (hb : d282284 q = 1) : d316359 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33908, d316359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33908, d316359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34081 q = 1) (hb : d282284 q = 1) : d316445 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34081, d316445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34081, d316445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34082 q = 1) (hb : d282284 q = 1) : d316446 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34082, d316446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34082, d316446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34083 q = 1) (hb : d282284 q = 1) : d316447 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34083, d316447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34083, d316447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83474 q ha hb
  have h8 (q : Pattern) (ha : d33918 q = 1) (hb : d282284 q = 1) : d316368 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33918, d316368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83474 q ha hb
    | true =>
      simp only [d33918, d316368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34084 q = 1) (hb : d282284 q = 1) : d316448 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34084, d316448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34084, d316448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33919 q = 1) (hb : d282284 q = 1) : d316369 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33919, d316369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33919, d316369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34085 q = 1) (hb : d282284 q = 1) : d316449 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34085, d316449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34085, d316449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34086 q = 1) (hb : d282284 q = 1) : d316450 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34086, d316450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34086, d316450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34087 q = 1) (hb : d282284 q = 1) : d316451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34087, d316451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34087, d316451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34088 q = 1) (hb : d282284 q = 1) : d316452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34088, d316452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34088, d316452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83475 q ha hb
  have h15 (q : Pattern) (ha : d33927 q = 1) (hb : d282284 q = 1) : d316377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33927, d316377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83475 q ha hb
    | true =>
      simp only [d33927, d316377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d34089 q = 1) (hb : d282284 q = 1) : d316453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34089, d316453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d34089, d316453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33928 q = 1) (hb : d282284 q = 1) : d316378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33928, d316378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33928, d316378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d34090 q = 1) (hb : d282284 q = 1) : d316454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34090, d316454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d34090, d316454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d34091 q = 1) (hb : d282284 q = 1) : d316455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34091, d316455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d34091, d316455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33718 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
  have h21 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d33719 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d33720 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33721 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d34092 q = 1) (hb : d282284 q = 1) : d316456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34092, d316456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d34092, d316456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d34093 q = 1) (hb : d282284 q = 1) : d316457 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34093, d316457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34093, d316457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro83491 (p : Pattern) (ha : d34099 p = 1) (hb : d282284 p = 1) : d316283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33709 q = 1) (hb : d282284 q = 1) : d316278 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33709, d316278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33709, d316278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
  have h2 (q : Pattern) (ha : d33567 q = 1) (hb : d282284 q = 1) : d316235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83419 q ha hb
    | true =>
      simp only [d33567, d316235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33710 q = 1) (hb : d282284 q = 1) : d316279 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33710, d316279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33710, d316279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33568 q = 1) (hb : d282284 q = 1) : d316236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33568, d316236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33711 q = 1) (hb : d282284 q = 1) : d316280 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33711, d316280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33711, d316280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33712 q = 1) (hb : d282284 q = 1) : d316281 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33712, d316281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33712, d316281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33713 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33713, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33713, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
  have h8 (q : Pattern) (ha : d33572 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83420 q ha hb
    | true =>
      simp only [d33572, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33714 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33714, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33714, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33573 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33573, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33715 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33715, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33715, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33716 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33716, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33716, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33717 q = 1) (hb : d282284 q = 1) : d316282 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33717, d316282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33717, d316282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33718 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
  have h15 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33719 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33720 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33721 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d34094 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
  have h21 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d34095 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d34096 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d34097 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d34098 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34098, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d34098, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d34099 q = 1) (hb : d282284 q = 1) : d316283 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34099, d316283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34099, d316283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro83492 (p : Pattern) (ha : d34104 p = 1) (hb : d282284 p = 1) : d286279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33718 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33718, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
  have h2 (q : Pattern) (ha : d33580 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83421 q ha hb
    | true =>
      simp only [d33580, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33719 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33719, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33581 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33581, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33720 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33720, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33721 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33721, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34094 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34094, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
  have h8 (q : Pattern) (ha : d33823 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83446 q ha hb
    | true =>
      simp only [d33823, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34095 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34095, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33824 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33824, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34096 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34096, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34097 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d34097, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d34098 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34098, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34098, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34103 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d34103, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d34104 q = 1) (hb : d282284 q = 1) : d286279 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d34104, d286279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d34104, d286279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83493 (p : Pattern) (ha : d34120 p = 1) (hb : d282284 p = 1) : d316466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34100 q = 1) (hb : d282284 q = 1) : d316458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34100, d316458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83490 q ha hb
    | true =>
      simp only [d34100, d316458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83491 q ha hb
  have h2 (q : Pattern) (ha : d34101 q = 1) (hb : d282284 q = 1) : d316459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34101, d316459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34101, d316459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34102 q = 1) (hb : d282284 q = 1) : d316460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34102, d316460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34102, d316460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34105 q = 1) (hb : d282284 q = 1) : d316461 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34105, d316461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83491 q ha hb
    | true =>
      simp only [d34105, d316461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83492 q ha hb
  have h5 (q : Pattern) (ha : d34106 q = 1) (hb : d282284 q = 1) : d316462 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34106, d316462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34106, d316462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34107 q = 1) (hb : d282284 q = 1) : d316463 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34107, d316463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34107, d316463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34108 q = 1) (hb : d282284 q = 1) : d316464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34108, d316464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34108, d316464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34111 q = 1) (hb : d282284 q = 1) : d316284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34111, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83491 q ha hb
    | true =>
      simp only [d34111, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83461 q ha hb
  have h9 (q : Pattern) (ha : d34112 q = 1) (hb : d282284 q = 1) : d316285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34112, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34112, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34113 q = 1) (hb : d282284 q = 1) : d316286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34113, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34113, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d34115 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83461 q ha hb
    | true =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83462 q ha hb
  have h12 (q : Pattern) (ha : d34116 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d34117 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d34118 q = 1) (hb : d282284 q = 1) : d316287 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34118, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34118, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d34119 q = 1) (hb : d282284 q = 1) : d316465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34119, d316465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34119, d316465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d34120 q = 1) (hb : d282284 q = 1) : d316466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34120, d316466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d34120, d316466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro83494 (p : Pattern) (ha : d34125 p = 1) (hb : d282284 p = 1) : d316470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34111 q = 1) (hb : d282284 q = 1) : d316284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34111, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83491 q ha hb
    | true =>
      simp only [d34111, d316284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83461 q ha hb
  have h2 (q : Pattern) (ha : d34112 q = 1) (hb : d282284 q = 1) : d316285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34112, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34112, d316285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34113 q = 1) (hb : d282284 q = 1) : d316286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34113, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34113, d316286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34115 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83461 q ha hb
    | true =>
      simp only [d34115, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83462 q ha hb
  have h5 (q : Pattern) (ha : d34116 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34116, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34117 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34117, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34118 q = 1) (hb : d282284 q = 1) : d316287 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34118, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34118, d316287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34123 q = 1) (hb : d282284 q = 1) : d286288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34123, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34123, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d34124 q = 1) (hb : d282284 q = 1) : d316469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d34124, d316469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34124, d316469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d34125 q = 1) (hb : d282284 q = 1) : d316470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d34125, d316470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d34125, d316470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro83495 (p : Pattern) (ha : d34131 p = 1) (hb : d282284 p = 1) : d316476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34121 q = 1) (hb : d282284 q = 1) : d316467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34121, d316467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83493 q ha hb
    | true =>
      simp only [d34121, d316467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34122 q = 1) (hb : d282284 q = 1) : d316468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34122, d316468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34122, d316468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34126 q = 1) (hb : d282284 q = 1) : d316471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83494 q ha hb
    | true =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34127 q = 1) (hb : d282284 q = 1) : d316472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34128 q = 1) (hb : d282284 q = 1) : d316473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34128, d316473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34128, d316473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34129 q = 1) (hb : d282284 q = 1) : d316474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34129, d316474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34129, d316474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34130 q = 1) (hb : d282284 q = 1) : d316475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34130, d316475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34130, d316475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34131 q = 1) (hb : d282284 q = 1) : d316476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34131, d316476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34131, d316476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83496 (p : Pattern) (ha : d34139 p = 1) (hb : d282284 p = 1) : d316480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34126 q = 1) (hb : d282284 q = 1) : d316471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83494 q ha hb
    | true =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34127 q = 1) (hb : d282284 q = 1) : d316472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34134 q = 1) (hb : d282284 q = 1) : d286299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34134, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83463 q ha hb
    | true =>
      simp only [d34134, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34135 q = 1) (hb : d282284 q = 1) : d286300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34135, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34135, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34136 q = 1) (hb : d282284 q = 1) : d316477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34136, d316477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34136, d316477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34137 q = 1) (hb : d282284 q = 1) : d316478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34137, d316478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34137, d316478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d34138 q = 1) (hb : d282284 q = 1) : d316479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34138, d316479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34138, d316479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34139 q = 1) (hb : d282284 q = 1) : d316480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34139, d316480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34139, d316480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83497 (p : Pattern) (ha : d34193 p = 1) (hb : d282284 p = 1) : d316486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34126 q = 1) (hb : d282284 q = 1) : d316471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83494 q ha hb
    | true =>
      simp only [d34126, d316471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d34127 q = 1) (hb : d282284 q = 1) : d316472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34127, d316472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34190 q = 1) (hb : d282284 q = 1) : d316483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d34190, d316483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34190, d316483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34191 q = 1) (hb : d282284 q = 1) : d316484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d34191, d316484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34191, d316484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d34192 q = 1) (hb : d282284 q = 1) : d316485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d34192, d316485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34192, d316485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d34193 q = 1) (hb : d282284 q = 1) : d316486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d34193, d316486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34193, d316486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83498 (p : Pattern) (ha : d266054 p = 1) (hb : d282284 p = 1) : d316492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34140 q = 1) (hb : d282284 q = 1) : d316481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34140, d316481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83495 q ha hb
    | true =>
      simp only [d34140, d316481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83496 q ha hb
  have h2 (q : Pattern) (ha : d266050 q = 1) (hb : d282284 q = 1) : d316482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d316482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266050, d316482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d34194 q = 1) (hb : d282284 q = 1) : d316487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34194, d316487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83497 q ha hb
    | true =>
      simp only [d34194, d316487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34195 q = 1) (hb : d282284 q = 1) : d316488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34195, d316488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34195, d316488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d282284 q = 1) : d316489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d316489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266051, d316489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d282284 q = 1) : d316490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d316490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d316490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d282284 q = 1) : d316491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d316491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d316491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d282284 q = 1) : d316492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d316492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d316492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83499 (p : Pattern) (ha : d266060 p = 1) (hb : d282284 p = 1) : d316498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33863 q = 1) (hb : d282284 q = 1) : d316329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33863, d316329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33863, d316329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83454 q ha hb
  have h2 (q : Pattern) (ha : d33864 q = 1) (hb : d282284 q = 1) : d316330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33864, d316330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33864, d316330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33873 q = 1) (hb : d282284 q = 1) : d316338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33873, d316338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83454 q ha hb
    | true =>
      simp only [d33873, d316338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83457 q ha hb
  have h4 (q : Pattern) (ha : d33874 q = 1) (hb : d282284 q = 1) : d316339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33874, d316339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33874, d316339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33875 q = 1) (hb : d282284 q = 1) : d316340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33875, d316340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33875, d316340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266038 q = 1) (hb : d282284 q = 1) : d316429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d316429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83481 q ha hb
    | true =>
      simp only [d266038, d316429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83488 q ha hb
  have h7 (q : Pattern) (ha : d34065 q = 1) (hb : d282284 q = 1) : d316431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34065, d316431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83458 q ha hb
    | true =>
      simp only [d34065, d316431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83459 q ha hb
  have h8 (q : Pattern) (ha : d266039 q = 1) (hb : d282284 q = 1) : d316432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d316432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266039, d316432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266040 q = 1) (hb : d282284 q = 1) : d316433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d316433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266040, d316433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d266041 q = 1) (hb : d282284 q = 1) : d316434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d316434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266041, d316434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266045 q = 1) (hb : d282284 q = 1) : d316438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d316438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266045, d316438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83489 q ha hb
  have h12 (q : Pattern) (ha : d34074 q = 1) (hb : d282284 q = 1) : d286256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34074, d286256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34074, d286256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83460 q ha hb
  have h13 (q : Pattern) (ha : d266046 q = 1) (hb : d282284 q = 1) : d316439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d316439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d266046, d316439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266047 q = 1) (hb : d282284 q = 1) : d316440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d316440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266047, d316440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d266048 q = 1) (hb : d282284 q = 1) : d316441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d316441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d266048, d316441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d266049 q = 1) (hb : d282284 q = 1) : d316442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d316442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266049, d316442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266055 q = 1) (hb : d282284 q = 1) : d316493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d316493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266055, d316493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83498 q ha hb
  have h18 (q : Pattern) (ha : d34211 q = 1) (hb : d282284 q = 1) : d286328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34211, d286328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34211, d286328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83465 q ha hb
  have h19 (q : Pattern) (ha : d266056 q = 1) (hb : d282284 q = 1) : d316494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d316494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266056, d316494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d266057 q = 1) (hb : d282284 q = 1) : d316495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d316495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d266057, d316495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d266058 q = 1) (hb : d282284 q = 1) : d316496 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d316496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d266058, d316496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d266059 q = 1) (hb : d282284 q = 1) : d316497 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d316497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d266059, d316497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d266060 q = 1) (hb : d282284 q = 1) : d316498 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d316498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266060, d316498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
end NetHack.Soko22Hazard87
