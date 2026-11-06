import NetHack.Soko22Hazard87.AndIntroBlocks0094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro23750 (p : Pattern) (ha : d129641 p = 1) (hb : d131065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129636 q = 1) (hb : d131060 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129636, d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23749 q ha hb
    | true =>
      simp only [d129636, d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129637 q = 1) (hb : d131061 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129637, d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129637, d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129638 q = 1) (hb : d131062 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129638, d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129638, d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129639 q = 1) (hb : d131063 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129639, d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129639, d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129640 q = 1) (hb : d131064 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129640, d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129640, d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129641 q = 1) (hb : d131065 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129641, d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129641, d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23751 (p : Pattern) (ha : d129647 p = 1) (hb : d131071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129642 q = 1) (hb : d131066 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129642, d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23750 q ha hb
    | true =>
      simp only [d129642, d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129643 q = 1) (hb : d131067 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129643, d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129643, d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129644 q = 1) (hb : d131068 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129644, d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129644, d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129645 q = 1) (hb : d131069 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129645, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129645, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129646 q = 1) (hb : d131070 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129646, d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129646, d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129647 q = 1) (hb : d131071 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129647, d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129647, d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23752 (p : Pattern) (ha : d129653 p = 1) (hb : d131077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129648 q = 1) (hb : d131072 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129648, d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23751 q ha hb
    | true =>
      simp only [d129648, d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129649 q = 1) (hb : d131073 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129649, d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129649, d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129650 q = 1) (hb : d131074 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129650, d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129650, d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129651 q = 1) (hb : d131075 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129651, d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129651, d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129652 q = 1) (hb : d131076 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129652, d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129652, d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129653 q = 1) (hb : d131077 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129653, d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129653, d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23753 (p : Pattern) (ha : d129659 p = 1) (hb : d131083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129654 q = 1) (hb : d131078 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23752 q ha hb
    | true =>
      simp only [d129654, d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129655 q = 1) (hb : d131079 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129656 q = 1) (hb : d131080 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129656, d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129657 q = 1) (hb : d131081 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129657, d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129658 q = 1) (hb : d131082 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129658, d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129659 q = 1) (hb : d131083 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129659, d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23754 (p : Pattern) (ha : d129665 p = 1) (hb : d131089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129660 q = 1) (hb : d131084 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23753 q ha hb
    | true =>
      simp only [d129660, d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129661 q = 1) (hb : d131085 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129662 q = 1) (hb : d131086 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129663 q = 1) (hb : d131087 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129664 q = 1) (hb : d131088 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129665 q = 1) (hb : d131089 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23755 (p : Pattern) (ha : d129671 p = 1) (hb : d131095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129666 q = 1) (hb : d131090 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23754 q ha hb
    | true =>
      simp only [d129666, d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129667 q = 1) (hb : d131091 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129668 q = 1) (hb : d131092 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129669 q = 1) (hb : d131093 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129670 q = 1) (hb : d131094 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129671 q = 1) (hb : d131095 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23756 (p : Pattern) (ha : d9296 p = 1) (hb : d131098 p = 1) : d30 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9292 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9293 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9294 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9295 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d9296 q = 1) (hb : d131098 q = 1) : d30 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9296, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9296, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro23757 (p : Pattern) (ha : d9302 p = 1) (hb : d131099 p = 1) : d131978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9298 q = 1) (hb : d131099 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9299 q = 1) (hb : d131099 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9300 q = 1) (hb : d131099 q = 1) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9301 q = 1) (hb : d131099 q = 1) : d18547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9301, d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9302 q = 1) (hb : d131099 q = 1) : d131978 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9302, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9302, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23758 (p : Pattern) (ha : d9308 p = 1) (hb : d131099 p = 1) : d131984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9303 q = 1) (hb : d131099 q = 1) : d131979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23757 q ha hb
    | true =>
      simp only [d9303, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9304 q = 1) (hb : d131099 q = 1) : d131980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9305 q = 1) (hb : d131099 q = 1) : d131981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9305, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9305, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9306 q = 1) (hb : d131099 q = 1) : d131982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9306, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9306, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9307 q = 1) (hb : d131099 q = 1) : d131983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9307, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9307, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9308 q = 1) (hb : d131099 q = 1) : d131984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9308, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9308, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23759 (p : Pattern) (ha : d9314 p = 1) (hb : d131099 p = 1) : d131990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23758 q ha hb
    | true =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9310 q = 1) (hb : d131099 q = 1) : d131986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9310, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9311 q = 1) (hb : d131099 q = 1) : d131987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9311, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9311, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9312 q = 1) (hb : d131099 q = 1) : d131988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9312, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9312, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9313 q = 1) (hb : d131099 q = 1) : d131989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9313, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9313, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9314 q = 1) (hb : d131099 q = 1) : d131990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9314, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9314, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23760 (p : Pattern) (ha : d9320 p = 1) (hb : d131099 p = 1) : d131996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9315 q = 1) (hb : d131099 q = 1) : d131991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9315, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9315, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23759 q ha hb
  have h2 (q : Pattern) (ha : d9316 q = 1) (hb : d131099 q = 1) : d131992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9316, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9316, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9317 q = 1) (hb : d131099 q = 1) : d131993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9317, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9317, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9318 q = 1) (hb : d131099 q = 1) : d131994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9318, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9318, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9319 q = 1) (hb : d131099 q = 1) : d131995 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9319, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9319, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9320 q = 1) (hb : d131099 q = 1) : d131996 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9320, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9320, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23761 (p : Pattern) (ha : d9329 p = 1) (hb : d131098 p = 1) : d144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9325 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9325, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d131098 q = 1) : d140 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9326 q = 1) (hb : d131098 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9326, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9326, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9327 q = 1) (hb : d131098 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9327, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9327, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9292 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9293 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9294 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9328 q = 1) (hb : d131098 q = 1) : d143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9328, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9328, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9295 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9329 q = 1) (hb : d131098 q = 1) : d144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9329, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9329, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23762 (p : Pattern) (ha : d9335 p = 1) (hb : d131099 p = 1) : d132001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9331 q = 1) (hb : d131099 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9332 q = 1) (hb : d131099 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9298 q = 1) (hb : d131099 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d9299 q = 1) (hb : d131099 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9333 q = 1) (hb : d131099 q = 1) : d18583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9300 q = 1) (hb : d131099 q = 1) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9334 q = 1) (hb : d131099 q = 1) : d18584 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9334, d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9335 q = 1) (hb : d131099 q = 1) : d132001 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9335, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9335, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro23763 (p : Pattern) (ha : d9341 p = 1) (hb : d131099 p = 1) : d132007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23762 q ha hb
    | true =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9303 q = 1) (hb : d131099 q = 1) : d131979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23757 q ha hb
    | true =>
      simp only [d9303, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9304 q = 1) (hb : d131099 q = 1) : d131980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9338 q = 1) (hb : d131099 q = 1) : d132004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9338, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9338, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9339 q = 1) (hb : d131099 q = 1) : d132005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9339, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9339, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9340 q = 1) (hb : d131099 q = 1) : d132006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9340, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9340, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9341 q = 1) (hb : d131099 q = 1) : d132007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9341, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9341, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23764 (p : Pattern) (ha : d101879 p = 1) (hb : d131099 p = 1) : d132013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d131099 q = 1) : d132008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23763 q ha hb
    | true =>
      simp only [d9342, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23758 q ha hb
  have h2 (q : Pattern) (ha : d101875 q = 1) (hb : d131099 q = 1) : d132009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101875, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101875, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9309 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23758 q ha hb
    | true =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9310 q = 1) (hb : d131099 q = 1) : d131986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9310, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101876 q = 1) (hb : d131099 q = 1) : d132010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101876, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101876, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101877 q = 1) (hb : d131099 q = 1) : d132011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101877, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101877, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101878 q = 1) (hb : d131099 q = 1) : d132012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101878, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101878, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101879 q = 1) (hb : d131099 q = 1) : d132013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101879, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101879, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23765 (p : Pattern) (ha : d101885 p = 1) (hb : d131099 p = 1) : d132019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101880 q = 1) (hb : d131099 q = 1) : d132014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101880, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101880, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23764 q ha hb
  have h2 (q : Pattern) (ha : d101881 q = 1) (hb : d131099 q = 1) : d132015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101881, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101881, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d101882 q = 1) (hb : d131099 q = 1) : d132016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101882, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101882, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d101883 q = 1) (hb : d131099 q = 1) : d132017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101883, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101883, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101884 q = 1) (hb : d131099 q = 1) : d132018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101884, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101884, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101885 q = 1) (hb : d131099 q = 1) : d132019 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101885, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101885, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23766 (p : Pattern) (ha : d9436 p = 1) (hb : d131099 p = 1) : d132049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23758 q ha hb
    | true =>
      simp only [d9309, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9432 q = 1) (hb : d131099 q = 1) : d132045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9432, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9433 q = 1) (hb : d131099 q = 1) : d132046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9433, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9434 q = 1) (hb : d131099 q = 1) : d132047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9435 q = 1) (hb : d131099 q = 1) : d132048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9436 q = 1) (hb : d131099 q = 1) : d132049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23767 (p : Pattern) (ha : d9388 p = 1) (hb : d131098 p = 1) : d15966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9377 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d131098 q = 1) : d320 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9378 q = 1) (hb : d131098 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9378, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9378, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9379 q = 1) (hb : d131098 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9379, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9379, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d139 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9325 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9325, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d140 q = 1) (hb : d131098 q = 1) : d140 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9326 q = 1) (hb : d131098 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9326, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9326, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9327 q = 1) (hb : d131098 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9327, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9327, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9380 q = 1) (hb : d131098 q = 1) : d323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9380, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9380, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9383 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9385 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9386 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9292 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9293 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9294 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9387 q = 1) (hb : d131098 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9387, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9387, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9388 q = 1) (hb : d131098 q = 1) : d15966 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9388, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9388, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23768 (p : Pattern) (ha : d9394 p = 1) (hb : d131099 p = 1) : d132025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9390 q = 1) (hb : d131099 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9391 q = 1) (hb : d131099 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d131099 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d131099 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9392 q = 1) (hb : d131099 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9298 q = 1) (hb : d131099 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9298, d131099, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d9299 q = 1) (hb : d131099 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9333 q = 1) (hb : d131099 q = 1) : d18583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9393 q = 1) (hb : d131099 q = 1) : d18648 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9393, d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9394 q = 1) (hb : d131099 q = 1) : d132025 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9394, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9394, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23769 (p : Pattern) (ha : d9400 p = 1) (hb : d131099 p = 1) : d132031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9395 q = 1) (hb : d131099 q = 1) : d132026 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9395, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23768 q ha hb
    | true =>
      simp only [d9395, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9396 q = 1) (hb : d131099 q = 1) : d132027 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9396, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9396, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9336 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23762 q ha hb
    | true =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9337 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9397 q = 1) (hb : d131099 q = 1) : d132028 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9397, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9397, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9398 q = 1) (hb : d131099 q = 1) : d132029 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9398, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9398, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9399 q = 1) (hb : d131099 q = 1) : d132030 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9399, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9399, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9400 q = 1) (hb : d131099 q = 1) : d132031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9400, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9400, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23770 (p : Pattern) (ha : d9424 p = 1) (hb : d131099 p = 1) : d132037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23762 q ha hb
    | true =>
      simp only [d9336, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9421 q = 1) (hb : d131099 q = 1) : d132034 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9421, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9421, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9422 q = 1) (hb : d131099 q = 1) : d132035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9422, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9422, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9423 q = 1) (hb : d131099 q = 1) : d132036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9423, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9423, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9424 q = 1) (hb : d131099 q = 1) : d132037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9424, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9424, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23771 (p : Pattern) (ha : d101895 p = 1) (hb : d131099 p = 1) : d132043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9401 q = 1) (hb : d131099 q = 1) : d132032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9401, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23769 q ha hb
    | true =>
      simp only [d9401, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23763 q ha hb
  have h2 (q : Pattern) (ha : d101891 q = 1) (hb : d131099 q = 1) : d132033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101891, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101891, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9425 q = 1) (hb : d131099 q = 1) : d132038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9425, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23770 q ha hb
    | true =>
      simp only [d9425, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9426 q = 1) (hb : d131099 q = 1) : d132039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9426, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9426, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101892 q = 1) (hb : d131099 q = 1) : d132040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101892, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101892, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101893 q = 1) (hb : d131099 q = 1) : d132041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101893, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101893, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101894 q = 1) (hb : d131099 q = 1) : d132042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101894, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101894, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101895 q = 1) (hb : d131099 q = 1) : d132043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101895, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101895, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23772 (p : Pattern) (ha : d101901 p = 1) (hb : d131099 p = 1) : d132055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101896 q = 1) (hb : d131099 q = 1) : d132044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101896, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101896, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23771 q ha hb
  have h2 (q : Pattern) (ha : d9437 q = 1) (hb : d131099 q = 1) : d132050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23766 q ha hb
  have h3 (q : Pattern) (ha : d101897 q = 1) (hb : d131099 q = 1) : d132051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101897, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101897, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101898 q = 1) (hb : d131099 q = 1) : d132052 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101898, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101898, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101899 q = 1) (hb : d131099 q = 1) : d132053 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101899, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101899, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101900 q = 1) (hb : d131099 q = 1) : d132054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101900, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101900, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101901 q = 1) (hb : d131099 q = 1) : d132055 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101901, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101901, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23773 (p : Pattern) (ha : d101907 p = 1) (hb : d131099 p = 1) : d132061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9321 q = 1) (hb : d131099 q = 1) : d131997 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9321, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9321, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23760 q ha hb
  have h2 (q : Pattern) (ha : d9322 q = 1) (hb : d131099 q = 1) : d131998 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9322, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9322, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9323 q = 1) (hb : d131099 q = 1) : d131999 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9323, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9323, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9324 q = 1) (hb : d131099 q = 1) : d132000 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9324, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9324, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101886 q = 1) (hb : d131099 q = 1) : d132020 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101886, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101886, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23765 q ha hb
  have h6 (q : Pattern) (ha : d101887 q = 1) (hb : d131099 q = 1) : d132021 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101887, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101887, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101888 q = 1) (hb : d131099 q = 1) : d132022 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101888, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101888, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101889 q = 1) (hb : d131099 q = 1) : d132023 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101889, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101889, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101890 q = 1) (hb : d131099 q = 1) : d132024 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101890, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101890, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101902 q = 1) (hb : d131099 q = 1) : d132056 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101902, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101902, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23772 q ha hb
  have h11 (q : Pattern) (ha : d101903 q = 1) (hb : d131099 q = 1) : d132057 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101903, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101903, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101904 q = 1) (hb : d131099 q = 1) : d132058 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101904, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101904, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101905 q = 1) (hb : d131099 q = 1) : d132059 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101905, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101905, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101906 q = 1) (hb : d131099 q = 1) : d132060 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101906, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101906, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101907 q = 1) (hb : d131099 q = 1) : d132061 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101907, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101907, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23774 (p : Pattern) (ha : d9497 p = 1) (hb : d131099 p = 1) : d132072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9331 q = 1) (hb : d131099 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9332 q = 1) (hb : d131099 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9487 q = 1) (hb : d131099 q = 1) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9496 q = 1) (hb : d131099 q = 1) : d18750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9496, d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9497 q = 1) (hb : d131099 q = 1) : d132072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9497, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9497, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23775 (p : Pattern) (ha : d9556 p = 1) (hb : d131099 p = 1) : d132095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9498 q = 1) (hb : d131099 q = 1) : d132073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23774 q ha hb
    | true =>
      simp only [d9498, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9499 q = 1) (hb : d131099 q = 1) : d132074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9553 q = 1) (hb : d131099 q = 1) : d132092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9553, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9553, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9554 q = 1) (hb : d131099 q = 1) : d132093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9554, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9554, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9555 q = 1) (hb : d131099 q = 1) : d132094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9555, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9555, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9556 q = 1) (hb : d131099 q = 1) : d132095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9556, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9556, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23776 (p : Pattern) (ha : d9562 p = 1) (hb : d131099 p = 1) : d132101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9557 q = 1) (hb : d131099 q = 1) : d132096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9557, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23775 q ha hb
    | true =>
      simp only [d9557, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9558 q = 1) (hb : d131099 q = 1) : d132097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9558, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9558, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9559 q = 1) (hb : d131099 q = 1) : d132098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9559, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9559, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9560 q = 1) (hb : d131099 q = 1) : d132099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9560, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9560, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9561 q = 1) (hb : d131099 q = 1) : d132100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9561, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9561, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9562 q = 1) (hb : d131099 q = 1) : d132101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9562, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9562, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23777 (p : Pattern) (ha : d9474 p = 1) (hb : d131098 p = 1) : d16077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9449 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d131098 q = 1) : d544 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9450 q = 1) (hb : d131098 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9450, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9450, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9451 q = 1) (hb : d131098 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9451, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9451, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9458 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9459 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9459, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9460 q = 1) (hb : d131098 q = 1) : d9460 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9461 q = 1) (hb : d131098 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9461, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9461, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9462 q = 1) (hb : d131098 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9462, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9462, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9463 q = 1) (hb : d131098 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9463, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9463, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9471 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9472 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9383 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9385 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9386 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9473 q = 1) (hb : d131098 q = 1) : d16076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9473, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9473, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9474 q = 1) (hb : d131098 q = 1) : d16077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9474, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9474, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23778 (p : Pattern) (ha : d9478 p = 1) (hb : d131098 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9383 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9383, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9385 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9385, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9386 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9386, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9292 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9293 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9293, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9294 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9294, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9387 q = 1) (hb : d131098 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9387, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9387, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9295 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9295, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9478 q = 1) (hb : d131098 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9478, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9478, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23779 (p : Pattern) (ha : d9484 p = 1) (hb : d131099 p = 1) : d132062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9475 q = 1) (hb : d131098 q = 1) : d16078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23777 q ha hb
    | true =>
      simp only [d9475, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9476 q = 1) (hb : d131099 q = 1) : d18729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d131099, d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9476, d131099, d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9477 q = 1) (hb : d131099 q = 1) : d18730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9479 q = 1) (hb : d131098 q = 1) : d16082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9479, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23778 q ha hb
  have h6 (q : Pattern) (ha : d9480 q = 1) (hb : d131099 q = 1) : d18731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d131099, d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9480, d131099, d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9481 q = 1) (hb : d131099 q = 1) : d18732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9482 q = 1) (hb : d131099 q = 1) : d18733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9482, d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h10 (q : Pattern) (ha : d9390 q = 1) (hb : d131099 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9391 q = 1) (hb : d131099 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h13 (q : Pattern) (ha : d9331 q = 1) (hb : d131099 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9332 q = 1) (hb : d131099 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9392 q = 1) (hb : d131099 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9483 q = 1) (hb : d131099 q = 1) : d18734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9483, d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9484 q = 1) (hb : d131099 q = 1) : d132062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9484, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9484, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23780 (p : Pattern) (ha : d9489 p = 1) (hb : d131099 p = 1) : d132065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9390 q = 1) (hb : d131099 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d131099, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9391 q = 1) (hb : d131099 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d131099 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9331, d131099, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d131099 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9392 q = 1) (hb : d131099 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9487 q = 1) (hb : d131099 q = 1) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9488 q = 1) (hb : d131099 q = 1) : d18741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9488, d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9489 q = 1) (hb : d131099 q = 1) : d132065 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9489, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9489, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23781 (p : Pattern) (ha : d9495 p = 1) (hb : d131099 p = 1) : d132071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9485 q = 1) (hb : d131099 q = 1) : d132063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9485, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23779 q ha hb
    | true =>
      simp only [d9485, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9486 q = 1) (hb : d131099 q = 1) : d132064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9486, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9486, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9490 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23780 q ha hb
    | true =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9491 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9492 q = 1) (hb : d131099 q = 1) : d132068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9492, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9492, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9493 q = 1) (hb : d131099 q = 1) : d132069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9493, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9493, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9494 q = 1) (hb : d131099 q = 1) : d132070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9494, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9494, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9495 q = 1) (hb : d131099 q = 1) : d132071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9495, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9495, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23782 (p : Pattern) (ha : d9503 p = 1) (hb : d131099 p = 1) : d132078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23780 q ha hb
    | true =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9498 q = 1) (hb : d131099 q = 1) : d132073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23774 q ha hb
    | true =>
      simp only [d9498, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9499 q = 1) (hb : d131099 q = 1) : d132074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9500 q = 1) (hb : d131099 q = 1) : d132075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9500, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9500, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9501 q = 1) (hb : d131099 q = 1) : d132076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9501, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9501, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9502 q = 1) (hb : d131099 q = 1) : d132077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9502, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9502, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9503 q = 1) (hb : d131099 q = 1) : d132078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9503, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9503, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23783 (p : Pattern) (ha : d9545 p = 1) (hb : d131099 p = 1) : d132084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23780 q ha hb
    | true =>
      simp only [d9490, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9542 q = 1) (hb : d131099 q = 1) : d132081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9542, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9542, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9543 q = 1) (hb : d131099 q = 1) : d132082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9543, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9543, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9544 q = 1) (hb : d131099 q = 1) : d132083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9544, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9544, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9545 q = 1) (hb : d131099 q = 1) : d132084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9545, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9545, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23784 (p : Pattern) (ha : d101912 p = 1) (hb : d131099 p = 1) : d132090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9504 q = 1) (hb : d131099 q = 1) : d132079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9504, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23781 q ha hb
    | true =>
      simp only [d9504, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23782 q ha hb
  have h2 (q : Pattern) (ha : d101908 q = 1) (hb : d131099 q = 1) : d132080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101908, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101908, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9546 q = 1) (hb : d131099 q = 1) : d132085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9546, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23783 q ha hb
    | true =>
      simp only [d9546, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9547 q = 1) (hb : d131099 q = 1) : d132086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9547, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9547, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101909 q = 1) (hb : d131099 q = 1) : d132087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101909, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101909, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101910 q = 1) (hb : d131099 q = 1) : d132088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101910, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101910, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101911 q = 1) (hb : d131099 q = 1) : d132089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101911, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101911, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101912 q = 1) (hb : d131099 q = 1) : d132090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101912, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101912, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23785 (p : Pattern) (ha : d101918 p = 1) (hb : d131099 p = 1) : d132107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101913 q = 1) (hb : d131099 q = 1) : d132091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101913, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101913, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23784 q ha hb
  have h2 (q : Pattern) (ha : d9563 q = 1) (hb : d131099 q = 1) : d132102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9563, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9563, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23776 q ha hb
  have h3 (q : Pattern) (ha : d101914 q = 1) (hb : d131099 q = 1) : d132103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101914, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101914, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101915 q = 1) (hb : d131099 q = 1) : d132104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101915, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101915, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101916 q = 1) (hb : d131099 q = 1) : d132105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101916, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101916, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101917 q = 1) (hb : d131099 q = 1) : d132106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101917, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101917, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101918 q = 1) (hb : d131099 q = 1) : d132107 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101918, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101918, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23786 (p : Pattern) (ha : d101924 p = 1) (hb : d131099 p = 1) : d132113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101919 q = 1) (hb : d131099 q = 1) : d132108 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101919, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101919, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23785 q ha hb
  have h2 (q : Pattern) (ha : d101920 q = 1) (hb : d131099 q = 1) : d132109 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101920, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101920, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101921 q = 1) (hb : d131099 q = 1) : d132110 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101921, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101921, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101922 q = 1) (hb : d131099 q = 1) : d132111 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101922, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101922, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101923 q = 1) (hb : d131099 q = 1) : d132112 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101923, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101923, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101924 q = 1) (hb : d131099 q = 1) : d132113 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101924, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101924, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23787 (p : Pattern) (ha : d9619 p = 1) (hb : d131098 p = 1) : d758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9377 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d131098 q = 1) : d320 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9378 q = 1) (hb : d131098 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9378, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9378, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9379 q = 1) (hb : d131098 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9379, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9379, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9604 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9605 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9606 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9618 q = 1) (hb : d131098 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9618, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9618, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9612 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9619 q = 1) (hb : d131098 q = 1) : d758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9619, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9619, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23788 (p : Pattern) (ha : d9623 p = 1) (hb : d131098 p = 1) : d762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9604 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9605 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9606 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9612 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d9623 q = 1) (hb : d131098 q = 1) : d762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9623, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9623, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro23789 (p : Pattern) (ha : d9642 p = 1) (hb : d131099 p = 1) : d132125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9625 q = 1) (hb : d131099 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9626 q = 1) (hb : d131099 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9632 q = 1) (hb : d131099 q = 1) : d18884 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9641 q = 1) (hb : d131099 q = 1) : d18894 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9641, d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9642 q = 1) (hb : d131099 q = 1) : d132125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9642, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9642, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23790 (p : Pattern) (ha : d9725 p = 1) (hb : d131099 p = 1) : d132148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9643 q = 1) (hb : d131099 q = 1) : d132126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23789 q ha hb
    | true =>
      simp only [d9643, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9644 q = 1) (hb : d131099 q = 1) : d132127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9722 q = 1) (hb : d131099 q = 1) : d132145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9722, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9722, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9723 q = 1) (hb : d131099 q = 1) : d132146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9723, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9723, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9724 q = 1) (hb : d131099 q = 1) : d132147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9724, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9724, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9725 q = 1) (hb : d131099 q = 1) : d132148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9725, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9725, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23791 (p : Pattern) (ha : d9731 p = 1) (hb : d131099 p = 1) : d132154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9726 q = 1) (hb : d131099 q = 1) : d132149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9726, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23790 q ha hb
    | true =>
      simp only [d9726, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9727 q = 1) (hb : d131099 q = 1) : d132150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9727, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9727, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9728 q = 1) (hb : d131099 q = 1) : d132151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9728, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9728, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9729 q = 1) (hb : d131099 q = 1) : d132152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9729, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9729, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9730 q = 1) (hb : d131099 q = 1) : d132153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9730, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9730, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9731 q = 1) (hb : d131099 q = 1) : d132154 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9731, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9731, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23792 (p : Pattern) (ha : d9603 p = 1) (hb : d131098 p = 1) : d16274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9576 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9576, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9576, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d835 q = 1) (hb : d131098 q = 1) : d835 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9577 q = 1) (hb : d131098 q = 1) : d836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9577, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9577, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9578 q = 1) (hb : d131098 q = 1) : d837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9578, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9578, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9587 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9588 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9588, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9588, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9589 q = 1) (hb : d131098 q = 1) : d9589 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9590 q = 1) (hb : d131098 q = 1) : d16270 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9590, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9590, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9591 q = 1) (hb : d131098 q = 1) : d16271 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9591, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9591, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9592 q = 1) (hb : d131098 q = 1) : d16272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9592, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9592, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9597 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9598 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9598, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9598, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9599 q = 1) (hb : d131098 q = 1) : d9599 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9600 q = 1) (hb : d131098 q = 1) : d14529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9600, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9600, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9601 q = 1) (hb : d131098 q = 1) : d14530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9601, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9601, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9471 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9472 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9602 q = 1) (hb : d131098 q = 1) : d16273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9602, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9602, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9603 q = 1) (hb : d131098 q = 1) : d16274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9603, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9603, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23793 (p : Pattern) (ha : d9608 p = 1) (hb : d131098 p = 1) : d16227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9449 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d131098 q = 1) : d544 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9450 q = 1) (hb : d131098 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9450, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9450, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9451 q = 1) (hb : d131098 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9451, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9451, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9458 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9459 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9459, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9460 q = 1) (hb : d131098 q = 1) : d9460 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9461 q = 1) (hb : d131098 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9461, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9461, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9462 q = 1) (hb : d131098 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9462, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9462, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9463 q = 1) (hb : d131098 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9463, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9463, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9471 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9472 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9604 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9605 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9606 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9607 q = 1) (hb : d131098 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9607, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9607, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9608 q = 1) (hb : d131098 q = 1) : d16227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9608, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9608, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23794 (p : Pattern) (ha : d9613 p = 1) (hb : d131098 p = 1) : d16278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9471 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9471, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9472 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9472, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9604 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9605 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9605, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9606 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9606, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9607 q = 1) (hb : d131098 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9607, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9607, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9612 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9612, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9613 q = 1) (hb : d131098 q = 1) : d16278 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9613, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9613, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23795 (p : Pattern) (ha : d9629 p = 1) (hb : d131099 p = 1) : d132115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9609 q = 1) (hb : d131098 q = 1) : d16275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23792 q ha hb
    | true =>
      simp only [d9609, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9610 q = 1) (hb : d131099 q = 1) : d18868 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d131099, d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9610, d131099, d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9611 q = 1) (hb : d131099 q = 1) : d18869 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9614 q = 1) (hb : d131098 q = 1) : d16279 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9614, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23794 q ha hb
  have h6 (q : Pattern) (ha : d9615 q = 1) (hb : d131099 q = 1) : d18870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d131099, d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9615, d131099, d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9616 q = 1) (hb : d131099 q = 1) : d18871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9617 q = 1) (hb : d131099 q = 1) : d18872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9617, d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9620 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
  have h10 (q : Pattern) (ha : d9621 q = 1) (hb : d131099 q = 1) : d18873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d131099, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9621, d131099, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9622 q = 1) (hb : d131099 q = 1) : d18874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h13 (q : Pattern) (ha : d9625 q = 1) (hb : d131099 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9626 q = 1) (hb : d131099 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9627 q = 1) (hb : d131099 q = 1) : d18877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9628 q = 1) (hb : d131099 q = 1) : d18878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9628, d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9629 q = 1) (hb : d131099 q = 1) : d132115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9629, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9629, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23796 (p : Pattern) (ha : d9634 p = 1) (hb : d131099 p = 1) : d132118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9620 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9621 q = 1) (hb : d131099 q = 1) : d18873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d131099, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9621, d131099, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9622 q = 1) (hb : d131099 q = 1) : d18874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h6 (q : Pattern) (ha : d9625 q = 1) (hb : d131099 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9625, d131099, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9626 q = 1) (hb : d131099 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9627 q = 1) (hb : d131099 q = 1) : d18877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9632 q = 1) (hb : d131099 q = 1) : d18884 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9633 q = 1) (hb : d131099 q = 1) : d18885 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9633, d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9634 q = 1) (hb : d131099 q = 1) : d132118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9634, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9634, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23797 (p : Pattern) (ha : d9640 p = 1) (hb : d131099 p = 1) : d132124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9630 q = 1) (hb : d131099 q = 1) : d132116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9630, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23795 q ha hb
    | true =>
      simp only [d9630, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9631 q = 1) (hb : d131099 q = 1) : d132117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9631, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9631, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9635 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23796 q ha hb
    | true =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9636 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9637 q = 1) (hb : d131099 q = 1) : d132121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9637, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9637, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9638 q = 1) (hb : d131099 q = 1) : d132122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9638, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9638, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9639 q = 1) (hb : d131099 q = 1) : d132123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9639, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9639, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9640 q = 1) (hb : d131099 q = 1) : d132124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9640, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9640, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23798 (p : Pattern) (ha : d9648 p = 1) (hb : d131099 p = 1) : d132131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23796 q ha hb
    | true =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9643 q = 1) (hb : d131099 q = 1) : d132126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23789 q ha hb
    | true =>
      simp only [d9643, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9644 q = 1) (hb : d131099 q = 1) : d132127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9645 q = 1) (hb : d131099 q = 1) : d132128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9645, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9645, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9646 q = 1) (hb : d131099 q = 1) : d132129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9646, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9646, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9647 q = 1) (hb : d131099 q = 1) : d132130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9647, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9647, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9648 q = 1) (hb : d131099 q = 1) : d132131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9648, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9648, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23799 (p : Pattern) (ha : d9714 p = 1) (hb : d131099 p = 1) : d132137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23796 q ha hb
    | true =>
      simp only [d9635, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9711 q = 1) (hb : d131099 q = 1) : d132134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9711, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9711, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9712 q = 1) (hb : d131099 q = 1) : d132135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9712, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9712, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9713 q = 1) (hb : d131099 q = 1) : d132136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9713, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9713, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9714 q = 1) (hb : d131099 q = 1) : d132137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9714, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9714, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23800 (p : Pattern) (ha : d101930 p = 1) (hb : d131099 p = 1) : d132143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9649 q = 1) (hb : d131099 q = 1) : d132132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9649, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23797 q ha hb
    | true =>
      simp only [d9649, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23798 q ha hb
  have h2 (q : Pattern) (ha : d101926 q = 1) (hb : d131099 q = 1) : d132133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101926, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101926, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9715 q = 1) (hb : d131099 q = 1) : d132138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9715, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23799 q ha hb
    | true =>
      simp only [d9715, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9716 q = 1) (hb : d131099 q = 1) : d132139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9716, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9716, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101927 q = 1) (hb : d131099 q = 1) : d132140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101927, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101927, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101928 q = 1) (hb : d131099 q = 1) : d132141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101928, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101928, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101929 q = 1) (hb : d131099 q = 1) : d132142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101929, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101929, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101930 q = 1) (hb : d131099 q = 1) : d132143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101930, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101930, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23801 (p : Pattern) (ha : d101936 p = 1) (hb : d131099 p = 1) : d132160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101931 q = 1) (hb : d131099 q = 1) : d132144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101931, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101931, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23800 q ha hb
  have h2 (q : Pattern) (ha : d9732 q = 1) (hb : d131099 q = 1) : d132155 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9732, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9732, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23791 q ha hb
  have h3 (q : Pattern) (ha : d101932 q = 1) (hb : d131099 q = 1) : d132156 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101932, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101932, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101933 q = 1) (hb : d131099 q = 1) : d132157 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101933, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101933, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101934 q = 1) (hb : d131099 q = 1) : d132158 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101934, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101934, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101935 q = 1) (hb : d131099 q = 1) : d132159 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101935, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101935, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101936 q = 1) (hb : d131099 q = 1) : d132160 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101936, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101936, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23802 (p : Pattern) (ha : d101942 p = 1) (hb : d131099 p = 1) : d132166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101937 q = 1) (hb : d131099 q = 1) : d132161 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101937, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23801 q ha hb
  have h2 (q : Pattern) (ha : d101938 q = 1) (hb : d131099 q = 1) : d132162 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101938, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101939 q = 1) (hb : d131099 q = 1) : d132163 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101939, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101940 q = 1) (hb : d131099 q = 1) : d132164 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101940, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101941 q = 1) (hb : d131099 q = 1) : d132165 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101941, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101942 q = 1) (hb : d131099 q = 1) : d132166 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101942, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23803 (p : Pattern) (ha : d9833 p = 1) (hb : d131098 p = 1) : d16443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9826 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9826, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9826, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d131098 q = 1) : d1111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9827 q = 1) (hb : d131098 q = 1) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9827, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9827, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9828 q = 1) (hb : d131098 q = 1) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9828, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9828, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9829 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9830 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9831 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9832 q = 1) (hb : d131098 q = 1) : d1125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9832, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9832, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9801 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9803 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9804 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d9820 q = 1) (hb : d131098 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9820, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d9833 q = 1) (hb : d131098 q = 1) : d16443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9833, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9833, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23804 (p : Pattern) (ha : d9869 p = 1) (hb : d131098 p = 1) : d14778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9829 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9830 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9831 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9868 q = 1) (hb : d131098 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9868, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9845 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9845, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d9846 q = 1) (hb : d131098 q = 1) : d9846 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9847 q = 1) (hb : d131098 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9847, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9848 q = 1) (hb : d131098 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9848, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d9849 q = 1) (hb : d131098 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9849, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9869 q = 1) (hb : d131098 q = 1) : d14778 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9869, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9869, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23805 (p : Pattern) (ha : d9875 p = 1) (hb : d131099 p = 1) : d132179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d131098 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9871 q = 1) (hb : d131099 q = 1) : d19088 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d131099, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9871, d131099, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9872 q = 1) (hb : d131099 q = 1) : d19089 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9873 q = 1) (hb : d131099 q = 1) : d19090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9874 q = 1) (hb : d131099 q = 1) : d19091 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9874, d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9875 q = 1) (hb : d131099 q = 1) : d132179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9875, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9875, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23806 (p : Pattern) (ha : d10010 p = 1) (hb : d131099 p = 1) : d132205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9876 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23805 q ha hb
    | true =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9877 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10007 q = 1) (hb : d131099 q = 1) : d132202 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10007, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10007, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10008 q = 1) (hb : d131099 q = 1) : d132203 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10008, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10008, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10009 q = 1) (hb : d131099 q = 1) : d132204 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10009, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10009, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10010 q = 1) (hb : d131099 q = 1) : d132205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10010, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10010, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23807 (p : Pattern) (ha : d10016 p = 1) (hb : d131099 p = 1) : d132211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10011 q = 1) (hb : d131099 q = 1) : d132206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10011, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23806 q ha hb
    | true =>
      simp only [d10011, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10012 q = 1) (hb : d131099 q = 1) : d132207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10012, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10012, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10013 q = 1) (hb : d131099 q = 1) : d132208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10013, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10013, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10014 q = 1) (hb : d131099 q = 1) : d132209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10014, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10014, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10015 q = 1) (hb : d131099 q = 1) : d132210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10015, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10015, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10016 q = 1) (hb : d131099 q = 1) : d132211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10016, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10016, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23808 (p : Pattern) (ha : d9784 p = 1) (hb : d131098 p = 1) : d16511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1210 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9746 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9746, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9746, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1211 q = 1) (hb : d131098 q = 1) : d1211 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9747 q = 1) (hb : d131098 q = 1) : d1212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9747, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9747, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9748 q = 1) (hb : d131098 q = 1) : d1213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9748, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9748, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9754 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9754, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9754, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9755 q = 1) (hb : d131098 q = 1) : d9755 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9756 q = 1) (hb : d131098 q = 1) : d16507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9756, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9756, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9757 q = 1) (hb : d131098 q = 1) : d16508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9757, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9757, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9758 q = 1) (hb : d131098 q = 1) : d16509 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9758, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9758, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9763 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9764 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9764, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9764, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9765 q = 1) (hb : d131098 q = 1) : d9765 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9766 q = 1) (hb : d131098 q = 1) : d14836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9766, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9766, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9767 q = 1) (hb : d131098 q = 1) : d14837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9767, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9767, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d9778 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9779 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9779, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d9780 q = 1) (hb : d131098 q = 1) : d9780 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9781 q = 1) (hb : d131098 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9781, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9782 q = 1) (hb : d131098 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9782, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9783 q = 1) (hb : d131098 q = 1) : d16510 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9783, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9783, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9784 q = 1) (hb : d131098 q = 1) : d16511 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9784, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9784, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23809 (p : Pattern) (ha : d9806 p = 1) (hb : d131098 p = 1) : d16442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9785 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9785, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9785, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d131098 q = 1) : d1101 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9786 q = 1) (hb : d131098 q = 1) : d1102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9786, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9786, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9787 q = 1) (hb : d131098 q = 1) : d1103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9787, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9787, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9789 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9790 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9790, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9790, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9791 q = 1) (hb : d131098 q = 1) : d9791 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9792 q = 1) (hb : d131098 q = 1) : d16438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9792, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9792, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9793 q = 1) (hb : d131098 q = 1) : d16439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9793, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9793, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9794 q = 1) (hb : d131098 q = 1) : d16440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9794, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9794, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9778 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9779 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9779, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d131098 q = 1) : d9780 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9781 q = 1) (hb : d131098 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9781, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9782 q = 1) (hb : d131098 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9782, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9801 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9803 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9804 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d9805 q = 1) (hb : d131098 q = 1) : d16441 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9805, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9805, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9806 q = 1) (hb : d131098 q = 1) : d16442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9806, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9806, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23810 (p : Pattern) (ha : d9821 p = 1) (hb : d131098 p = 1) : d16516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9815 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9815, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9815, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9816 q = 1) (hb : d131098 q = 1) : d9816 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9817 q = 1) (hb : d131098 q = 1) : d13022 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9817, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9817, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9818 q = 1) (hb : d131098 q = 1) : d13023 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9818, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9818, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9801 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9803 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9803, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9804 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9804, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d9819 q = 1) (hb : d131098 q = 1) : d16515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9819, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9819, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9820 q = 1) (hb : d131098 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9820, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9821 q = 1) (hb : d131098 q = 1) : d16516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9821, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9821, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23811 (p : Pattern) (ha : d9850 p = 1) (hb : d131098 p = 1) : d14773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9837 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9837, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9837, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5019 q = 1) (hb : d131098 q = 1) : d5019 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9838 q = 1) (hb : d131098 q = 1) : d5020 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9838, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9838, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9839 q = 1) (hb : d131098 q = 1) : d5021 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9839, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9839, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9840 q = 1) (hb : d131098 q = 1) : d5022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9840, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9840, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9845 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9845, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d9846 q = 1) (hb : d131098 q = 1) : d9846 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9847 q = 1) (hb : d131098 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9847, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9848 q = 1) (hb : d131098 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9848, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d9849 q = 1) (hb : d131098 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9849, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d9850 q = 1) (hb : d131098 q = 1) : d14773 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9850, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9850, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23812 (p : Pattern) (ha : d9856 p = 1) (hb : d131099 p = 1) : d132169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9807 q = 1) (hb : d131098 q = 1) : d16512 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23808 q ha hb
    | true =>
      simp only [d9807, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9808 q = 1) (hb : d131099 q = 1) : d19056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d131099, d19056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9808, d131099, d19056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9809 q = 1) (hb : d131099 q = 1) : d19057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d19057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, d19057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9822 q = 1) (hb : d131098 q = 1) : d16517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
    | true =>
      simp only [d9822, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23810 q ha hb
  have h6 (q : Pattern) (ha : d9823 q = 1) (hb : d131099 q = 1) : d19058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d131099, d19058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9823, d131099, d19058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9824 q = 1) (hb : d131099 q = 1) : d19059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d19059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, d19059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9825 q = 1) (hb : d131099 q = 1) : d19060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d19060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9825, d19060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9834 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
    | true =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
  have h10 (q : Pattern) (ha : d9835 q = 1) (hb : d131099 q = 1) : d19061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9836 q = 1) (hb : d131099 q = 1) : d19062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9851 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23811 q ha hb
  have h13 (q : Pattern) (ha : d9852 q = 1) (hb : d131099 q = 1) : d19063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9853 q = 1) (hb : d131099 q = 1) : d19064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9854 q = 1) (hb : d131099 q = 1) : d19065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9855 q = 1) (hb : d131099 q = 1) : d19066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d19066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9855, d19066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9856 q = 1) (hb : d131099 q = 1) : d132169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9856, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9856, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23813 (p : Pattern) (ha : d9861 p = 1) (hb : d131099 p = 1) : d132172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
    | true =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d131099 q = 1) : d19061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d131099 q = 1) : d19062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23811 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d131099 q = 1) : d19063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d131099 q = 1) : d19064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d131099 q = 1) : d19065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9859 q = 1) (hb : d131099 q = 1) : d19072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d19072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9859, d19072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9860 q = 1) (hb : d131099 q = 1) : d19073 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d19073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9860, d19073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9861 q = 1) (hb : d131099 q = 1) : d132172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9861, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9861, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23814 (p : Pattern) (ha : d9867 p = 1) (hb : d131099 p = 1) : d132178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9857 q = 1) (hb : d131099 q = 1) : d132170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9857, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23812 q ha hb
    | true =>
      simp only [d9857, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9858 q = 1) (hb : d131099 q = 1) : d132171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9858, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9858, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9862 q = 1) (hb : d131099 q = 1) : d132173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23813 q ha hb
    | true =>
      simp only [d9862, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9863 q = 1) (hb : d131099 q = 1) : d132174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9864 q = 1) (hb : d131099 q = 1) : d132175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9864, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9864, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9865 q = 1) (hb : d131099 q = 1) : d132176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9865, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9865, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9866 q = 1) (hb : d131099 q = 1) : d132177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9866, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9866, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9867 q = 1) (hb : d131099 q = 1) : d132178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9867, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9867, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23815 (p : Pattern) (ha : d9881 p = 1) (hb : d131099 p = 1) : d132185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9862 q = 1) (hb : d131099 q = 1) : d132173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23813 q ha hb
    | true =>
      simp only [d9862, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9863 q = 1) (hb : d131099 q = 1) : d132174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23805 q ha hb
    | true =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9878 q = 1) (hb : d131099 q = 1) : d132182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9878, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9878, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9879 q = 1) (hb : d131099 q = 1) : d132183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9879, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9879, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9880 q = 1) (hb : d131099 q = 1) : d132184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9880, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9880, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9881 q = 1) (hb : d131099 q = 1) : d132185 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9881, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9881, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23816 (p : Pattern) (ha : d9987 p = 1) (hb : d131098 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9829 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9830 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9830, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9831 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9831, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9868 q = 1) (hb : d131098 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9868, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d9987 q = 1) (hb : d131098 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9987, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9987, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro23817 (p : Pattern) (ha : d9993 p = 1) (hb : d131099 p = 1) : d132188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
    | true =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d131099 q = 1) : d19061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d131099 q = 1) : d19062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23811 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d131099 q = 1) : d19063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d131099 q = 1) : d19064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d131099 q = 1) : d19065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9988 q = 1) (hb : d131098 q = 1) : d16574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9988, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23816 q ha hb
  have h10 (q : Pattern) (ha : d9989 q = 1) (hb : d131099 q = 1) : d19180 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d131099, d19180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9989, d131099, d19180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9990 q = 1) (hb : d131099 q = 1) : d19181 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d19181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, d19181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9991 q = 1) (hb : d131099 q = 1) : d19182 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d19182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9991, d19182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9992 q = 1) (hb : d131099 q = 1) : d19183 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d19183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9992, d19183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9993 q = 1) (hb : d131099 q = 1) : d132188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9993, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9993, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23818 (p : Pattern) (ha : d9999 p = 1) (hb : d131099 p = 1) : d132194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9994 q = 1) (hb : d131099 q = 1) : d132189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9994, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23817 q ha hb
    | true =>
      simp only [d9994, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9995 q = 1) (hb : d131099 q = 1) : d132190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9995, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9995, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9996 q = 1) (hb : d131099 q = 1) : d132191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9996, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9996, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9997 q = 1) (hb : d131099 q = 1) : d132192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9997, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9997, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9998 q = 1) (hb : d131099 q = 1) : d132193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9998, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9998, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9999 q = 1) (hb : d131099 q = 1) : d132194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9999, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9999, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23819 (p : Pattern) (ha : d101949 p = 1) (hb : d131099 p = 1) : d132200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9882 q = 1) (hb : d131099 q = 1) : d132186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9882, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23814 q ha hb
    | true =>
      simp only [d9882, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23815 q ha hb
  have h2 (q : Pattern) (ha : d101945 q = 1) (hb : d131099 q = 1) : d132187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101945, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10000 q = 1) (hb : d131099 q = 1) : d132195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10000, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23818 q ha hb
    | true =>
      simp only [d10000, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10001 q = 1) (hb : d131099 q = 1) : d132196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10001, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10001, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101946 q = 1) (hb : d131099 q = 1) : d132197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101946, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101947 q = 1) (hb : d131099 q = 1) : d132198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101947, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101948 q = 1) (hb : d131099 q = 1) : d132199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101948, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101949 q = 1) (hb : d131099 q = 1) : d132200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101949, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23820 (p : Pattern) (ha : d101955 p = 1) (hb : d131099 p = 1) : d132217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101950 q = 1) (hb : d131099 q = 1) : d132201 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101950, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23819 q ha hb
  have h2 (q : Pattern) (ha : d10017 q = 1) (hb : d131099 q = 1) : d132212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10017, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10017, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23807 q ha hb
  have h3 (q : Pattern) (ha : d101951 q = 1) (hb : d131099 q = 1) : d132213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101952 q = 1) (hb : d131099 q = 1) : d132214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101953 q = 1) (hb : d131099 q = 1) : d132215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101954 q = 1) (hb : d131099 q = 1) : d132216 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101955 q = 1) (hb : d131099 q = 1) : d132217 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101955, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23821 (p : Pattern) (ha : d101961 p = 1) (hb : d131099 p = 1) : d132223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101956 q = 1) (hb : d131099 q = 1) : d132218 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101956, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23820 q ha hb
  have h2 (q : Pattern) (ha : d101957 q = 1) (hb : d131099 q = 1) : d132219 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101957, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101958 q = 1) (hb : d131099 q = 1) : d132220 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101958, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101959 q = 1) (hb : d131099 q = 1) : d132221 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101959, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101960 q = 1) (hb : d131099 q = 1) : d132222 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101960, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101961 q = 1) (hb : d131099 q = 1) : d132223 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101961, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23822 (p : Pattern) (ha : d10121 p = 1) (hb : d131098 p = 1) : d16795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1570 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10111 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10111, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10111, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d131098 q = 1) : d1571 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10112 q = 1) (hb : d131098 q = 1) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10112, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10112, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10113 q = 1) (hb : d131098 q = 1) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10113, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10113, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10115 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10116 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10116, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10116, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10117 q = 1) (hb : d131098 q = 1) : d10117 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10118 q = 1) (hb : d131098 q = 1) : d16792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10118, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10118, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10119 q = 1) (hb : d131098 q = 1) : d16793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10119, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10119, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10120 q = 1) (hb : d131098 q = 1) : d16794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10120, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10120, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10086 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10088 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10089 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10105 q = 1) (hb : d131098 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10105, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d10121 q = 1) (hb : d131098 q = 1) : d16795 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10121, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10121, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23823 (p : Pattern) (ha : d10163 p = 1) (hb : d131098 p = 1) : d15171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d131098 q = 1) : d1583 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10160 q = 1) (hb : d131098 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10160, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d131098 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10161, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d131098 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10137 q = 1) (hb : d131098 q = 1) : d10137 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10138 q = 1) (hb : d131098 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10138, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10139 q = 1) (hb : d131098 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10139, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10140 q = 1) (hb : d131098 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10140, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10163 q = 1) (hb : d131098 q = 1) : d15171 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10163, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10163, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23824 (p : Pattern) (ha : d10169 p = 1) (hb : d131099 p = 1) : d132237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10164 q = 1) (hb : d131098 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10164, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23823 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10165 q = 1) (hb : d131099 q = 1) : d19323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d131099, d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10165, d131099, d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10166 q = 1) (hb : d131099 q = 1) : d19324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10167 q = 1) (hb : d131099 q = 1) : d19325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10167, d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10168 q = 1) (hb : d131099 q = 1) : d19326 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d19326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10168, d19326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10169 q = 1) (hb : d131099 q = 1) : d132237 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10169, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10169, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23825 (p : Pattern) (ha : d10316 p = 1) (hb : d131099 p = 1) : d132263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10170 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23824 q ha hb
    | true =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10171 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10313 q = 1) (hb : d131099 q = 1) : d132260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10313, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10313, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10314 q = 1) (hb : d131099 q = 1) : d132261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10314, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10314, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10315 q = 1) (hb : d131099 q = 1) : d132262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10315, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10315, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10316 q = 1) (hb : d131099 q = 1) : d132263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10316, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10316, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23826 (p : Pattern) (ha : d10322 p = 1) (hb : d131099 p = 1) : d132269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10317 q = 1) (hb : d131099 q = 1) : d132264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10317, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23825 q ha hb
    | true =>
      simp only [d10317, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10318 q = 1) (hb : d131099 q = 1) : d132265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10318, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10318, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10319 q = 1) (hb : d131099 q = 1) : d132266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10319, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10319, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10320 q = 1) (hb : d131099 q = 1) : d132267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10320, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10320, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10321 q = 1) (hb : d131099 q = 1) : d132268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10321, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10321, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10322 q = 1) (hb : d131099 q = 1) : d132269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10322, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10322, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23827 (p : Pattern) (ha : d10069 p = 1) (hb : d131098 p = 1) : d16863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10032 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10032, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10032, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1666 q = 1) (hb : d131098 q = 1) : d1666 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10033 q = 1) (hb : d131098 q = 1) : d1667 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10033, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10033, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10034 q = 1) (hb : d131098 q = 1) : d1668 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10034, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10034, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10036 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10037 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10037, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10037, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10038 q = 1) (hb : d131098 q = 1) : d10038 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10039 q = 1) (hb : d131098 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10039, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10039, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10040 q = 1) (hb : d131098 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10040, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10040, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10041 q = 1) (hb : d131098 q = 1) : d16861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10041, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10041, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10046 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10047 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10047, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10047, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10048 q = 1) (hb : d131098 q = 1) : d10048 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10049 q = 1) (hb : d131098 q = 1) : d15229 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10049, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10049, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10050 q = 1) (hb : d131098 q = 1) : d15230 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10050, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10050, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10064 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d10065 q = 1) (hb : d131098 q = 1) : d10065 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10066 q = 1) (hb : d131098 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10066, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10067 q = 1) (hb : d131098 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10067, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10068 q = 1) (hb : d131098 q = 1) : d16862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10068, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10068, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10069 q = 1) (hb : d131098 q = 1) : d16863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10069, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10069, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23828 (p : Pattern) (ha : d10091 p = 1) (hb : d131098 p = 1) : d16791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10070 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10070, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10070, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d131098 q = 1) : d1556 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10071 q = 1) (hb : d131098 q = 1) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10071, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10071, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10072 q = 1) (hb : d131098 q = 1) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10072, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10072, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10074 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10075 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10075, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10075, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10076 q = 1) (hb : d131098 q = 1) : d10076 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10077 q = 1) (hb : d131098 q = 1) : d16787 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10077, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10077, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10078 q = 1) (hb : d131098 q = 1) : d16788 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10078, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10078, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10079 q = 1) (hb : d131098 q = 1) : d16789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10079, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10079, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10064 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10065 q = 1) (hb : d131098 q = 1) : d10065 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10066 q = 1) (hb : d131098 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10066, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10067 q = 1) (hb : d131098 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10067, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10086 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10088 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10089 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10090 q = 1) (hb : d131098 q = 1) : d16790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10090, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10090, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10091 q = 1) (hb : d131098 q = 1) : d16791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10091, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10091, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23829 (p : Pattern) (ha : d10106 p = 1) (hb : d131098 p = 1) : d16868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10100 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10100, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10100, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10101 q = 1) (hb : d131098 q = 1) : d10101 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10102 q = 1) (hb : d131098 q = 1) : d13348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10102, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10102, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10103 q = 1) (hb : d131098 q = 1) : d13349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10103, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10103, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10086 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10088 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10088, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10089 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10089, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10104 q = 1) (hb : d131098 q = 1) : d16867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10104, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10104, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10105 q = 1) (hb : d131098 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10105, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10106 q = 1) (hb : d131098 q = 1) : d16868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10106, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10106, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23830 (p : Pattern) (ha : d10141 p = 1) (hb : d131098 p = 1) : d15166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10125 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10125, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10125, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5135 q = 1) (hb : d131098 q = 1) : d5135 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10126 q = 1) (hb : d131098 q = 1) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10126, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10126, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10127 q = 1) (hb : d131098 q = 1) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10127, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10127, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10128 q = 1) (hb : d131098 q = 1) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10128, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10128, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10137 q = 1) (hb : d131098 q = 1) : d10137 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10138 q = 1) (hb : d131098 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10138, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10139 q = 1) (hb : d131098 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10139, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10140 q = 1) (hb : d131098 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10140, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10141 q = 1) (hb : d131098 q = 1) : d15166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10141, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10141, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23831 (p : Pattern) (ha : d10147 p = 1) (hb : d131099 p = 1) : d132227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10092 q = 1) (hb : d131098 q = 1) : d16864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23827 q ha hb
    | true =>
      simp only [d10092, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10093 q = 1) (hb : d131099 q = 1) : d19288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d131099, d19288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10093, d131099, d19288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10094 q = 1) (hb : d131099 q = 1) : d19289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d19289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, d19289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10107 q = 1) (hb : d131098 q = 1) : d16869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
    | true =>
      simp only [d10107, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23829 q ha hb
  have h6 (q : Pattern) (ha : d10108 q = 1) (hb : d131099 q = 1) : d19290 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d131099, d19290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10108, d131099, d19290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10109 q = 1) (hb : d131099 q = 1) : d19291 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d19291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, d19291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10110 q = 1) (hb : d131099 q = 1) : d19292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d19292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10110, d19292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10122 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
    | true =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
  have h10 (q : Pattern) (ha : d10123 q = 1) (hb : d131099 q = 1) : d19293 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10124 q = 1) (hb : d131099 q = 1) : d19294 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10142 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23830 q ha hb
  have h13 (q : Pattern) (ha : d10143 q = 1) (hb : d131099 q = 1) : d19295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d10144 q = 1) (hb : d131099 q = 1) : d19296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10145 q = 1) (hb : d131099 q = 1) : d19297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10146 q = 1) (hb : d131099 q = 1) : d19298 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d19298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10146, d19298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10147 q = 1) (hb : d131099 q = 1) : d132227 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10147, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10147, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23832 (p : Pattern) (ha : d10152 p = 1) (hb : d131099 p = 1) : d132230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
    | true =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d131099 q = 1) : d19293 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d131099 q = 1) : d19294 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23830 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d131099 q = 1) : d19295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d131099 q = 1) : d19296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d131099 q = 1) : d19297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10150 q = 1) (hb : d131099 q = 1) : d19304 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d19304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10150, d19304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10151 q = 1) (hb : d131099 q = 1) : d19305 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d19305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10151, d19305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10152 q = 1) (hb : d131099 q = 1) : d132230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10152, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10152, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23833 (p : Pattern) (ha : d10158 p = 1) (hb : d131099 p = 1) : d132236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10148 q = 1) (hb : d131099 q = 1) : d132228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10148, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23831 q ha hb
    | true =>
      simp only [d10148, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10149 q = 1) (hb : d131099 q = 1) : d132229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10149, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10149, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10153 q = 1) (hb : d131099 q = 1) : d132231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23832 q ha hb
    | true =>
      simp only [d10153, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10154 q = 1) (hb : d131099 q = 1) : d132232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10155 q = 1) (hb : d131099 q = 1) : d132233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10155, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10155, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10156 q = 1) (hb : d131099 q = 1) : d132234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10156, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10156, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10157 q = 1) (hb : d131099 q = 1) : d132235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10157, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10157, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10158 q = 1) (hb : d131099 q = 1) : d132236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10158, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10158, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23834 (p : Pattern) (ha : d10175 p = 1) (hb : d131099 p = 1) : d132243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10153 q = 1) (hb : d131099 q = 1) : d132231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23832 q ha hb
    | true =>
      simp only [d10153, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10154 q = 1) (hb : d131099 q = 1) : d132232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23824 q ha hb
    | true =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10172 q = 1) (hb : d131099 q = 1) : d132240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10172, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10172, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10173 q = 1) (hb : d131099 q = 1) : d132241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10173, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10173, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10174 q = 1) (hb : d131099 q = 1) : d132242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10174, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10174, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10175 q = 1) (hb : d131099 q = 1) : d132243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10175, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10175, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23835 (p : Pattern) (ha : d10293 p = 1) (hb : d131098 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d131098 q = 1) : d1583 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10160 q = 1) (hb : d131098 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10160, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d131098 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10161, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d131098 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10293 q = 1) (hb : d131098 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10293, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10293, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro23836 (p : Pattern) (ha : d10299 p = 1) (hb : d131099 p = 1) : d132246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
    | true =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d131099 q = 1) : d19293 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d131099 q = 1) : d19294 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23830 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d131099 q = 1) : d19295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d131099 q = 1) : d19296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d131099 q = 1) : d19297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10294 q = 1) (hb : d131098 q = 1) : d16929 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10294, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23835 q ha hb
  have h10 (q : Pattern) (ha : d10295 q = 1) (hb : d131099 q = 1) : d19418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d131099, d19418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10295, d131099, d19418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10296 q = 1) (hb : d131099 q = 1) : d19419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d19419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, d19419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10297 q = 1) (hb : d131099 q = 1) : d19420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d19420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10297, d19420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10298 q = 1) (hb : d131099 q = 1) : d19421 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d19421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10298, d19421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10299 q = 1) (hb : d131099 q = 1) : d132246 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10299, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10299, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23837 (p : Pattern) (ha : d10305 p = 1) (hb : d131099 p = 1) : d132252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10300 q = 1) (hb : d131099 q = 1) : d132247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10300, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23836 q ha hb
    | true =>
      simp only [d10300, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10301 q = 1) (hb : d131099 q = 1) : d132248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10301, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10301, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10302 q = 1) (hb : d131099 q = 1) : d132249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10302, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10302, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10303 q = 1) (hb : d131099 q = 1) : d132250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10303, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10303, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10304 q = 1) (hb : d131099 q = 1) : d132251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10304, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10304, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10305 q = 1) (hb : d131099 q = 1) : d132252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10305, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10305, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23838 (p : Pattern) (ha : d101969 p = 1) (hb : d131099 p = 1) : d132258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10176 q = 1) (hb : d131099 q = 1) : d132244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10176, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23833 q ha hb
    | true =>
      simp only [d10176, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23834 q ha hb
  have h2 (q : Pattern) (ha : d101965 q = 1) (hb : d131099 q = 1) : d132245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101965, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10306 q = 1) (hb : d131099 q = 1) : d132253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10306, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23837 q ha hb
    | true =>
      simp only [d10306, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10307 q = 1) (hb : d131099 q = 1) : d132254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10307, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10307, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101966 q = 1) (hb : d131099 q = 1) : d132255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101966, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101967 q = 1) (hb : d131099 q = 1) : d132256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101967, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101968 q = 1) (hb : d131099 q = 1) : d132257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101968, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101969 q = 1) (hb : d131099 q = 1) : d132258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101969, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23839 (p : Pattern) (ha : d101975 p = 1) (hb : d131099 p = 1) : d132275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101970 q = 1) (hb : d131099 q = 1) : d132259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101970, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23838 q ha hb
  have h2 (q : Pattern) (ha : d10323 q = 1) (hb : d131099 q = 1) : d132270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10323, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10323, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23826 q ha hb
  have h3 (q : Pattern) (ha : d101971 q = 1) (hb : d131099 q = 1) : d132271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101972 q = 1) (hb : d131099 q = 1) : d132272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101973 q = 1) (hb : d131099 q = 1) : d132273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101974 q = 1) (hb : d131099 q = 1) : d132274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101975 q = 1) (hb : d131099 q = 1) : d132275 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101975, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23840 (p : Pattern) (ha : d101981 p = 1) (hb : d131099 p = 1) : d132281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101976 q = 1) (hb : d131099 q = 1) : d132276 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101976, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23839 q ha hb
  have h2 (q : Pattern) (ha : d101977 q = 1) (hb : d131099 q = 1) : d132277 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101977, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101978 q = 1) (hb : d131099 q = 1) : d132278 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101978, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101979 q = 1) (hb : d131099 q = 1) : d132279 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101979, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101980 q = 1) (hb : d131099 q = 1) : d132280 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101980, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101981 q = 1) (hb : d131099 q = 1) : d132281 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101981, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23841 (p : Pattern) (ha : d10397 p = 1) (hb : d131098 p = 1) : d17161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10387 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10387, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10387, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2054 q = 1) (hb : d131098 q = 1) : d2054 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10388 q = 1) (hb : d131098 q = 1) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10388, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10388, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10389 q = 1) (hb : d131098 q = 1) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10389, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10389, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10391 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10392 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10392, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10392, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10393 q = 1) (hb : d131098 q = 1) : d10393 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10394 q = 1) (hb : d131098 q = 1) : d17158 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10394, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10394, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10395 q = 1) (hb : d131098 q = 1) : d17159 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10395, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10395, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10396 q = 1) (hb : d131098 q = 1) : d17160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10396, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10396, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10372 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10374 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10375 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10381 q = 1) (hb : d131098 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10381, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d10397 q = 1) (hb : d131098 q = 1) : d17161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10397, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10397, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23842 (p : Pattern) (ha : d10440 p = 1) (hb : d131098 p = 1) : d15563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d131098 q = 1) : d2066 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10437 q = 1) (hb : d131098 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10437, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d131098 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10438, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d131098 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10414 q = 1) (hb : d131098 q = 1) : d10414 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10415 q = 1) (hb : d131098 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10415, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10416 q = 1) (hb : d131098 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10416, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10417 q = 1) (hb : d131098 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10417, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10440 q = 1) (hb : d131098 q = 1) : d15563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10440, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10440, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23843 (p : Pattern) (ha : d10446 p = 1) (hb : d131099 p = 1) : d132296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10441 q = 1) (hb : d131098 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10441, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23842 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10442 q = 1) (hb : d131099 q = 1) : d19555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d131099, d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10442, d131099, d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10443 q = 1) (hb : d131099 q = 1) : d19556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10444 q = 1) (hb : d131099 q = 1) : d19557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10444, d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10445 q = 1) (hb : d131099 q = 1) : d19558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d19558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10445, d19558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10446 q = 1) (hb : d131099 q = 1) : d132296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10446, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10446, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23844 (p : Pattern) (ha : d10582 p = 1) (hb : d131099 p = 1) : d132322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10447 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23843 q ha hb
    | true =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10448 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10579 q = 1) (hb : d131099 q = 1) : d132319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10579, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10579, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10580 q = 1) (hb : d131099 q = 1) : d132320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10580, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10580, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10581 q = 1) (hb : d131099 q = 1) : d132321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10581, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10581, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10582 q = 1) (hb : d131099 q = 1) : d132322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10582, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10582, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23845 (p : Pattern) (ha : d10588 p = 1) (hb : d131099 p = 1) : d132328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10583 q = 1) (hb : d131099 q = 1) : d132323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10583, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23844 q ha hb
    | true =>
      simp only [d10583, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10584 q = 1) (hb : d131099 q = 1) : d132324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10584, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10584, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10585 q = 1) (hb : d131099 q = 1) : d132325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10585, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10585, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10586 q = 1) (hb : d131099 q = 1) : d132326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10586, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10586, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10587 q = 1) (hb : d131099 q = 1) : d132327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10587, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10587, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10588 q = 1) (hb : d131099 q = 1) : d132328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10588, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10588, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23846 (p : Pattern) (ha : d10359 p = 1) (hb : d131098 p = 1) : d17229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10339 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10339, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10339, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2145 q = 1) (hb : d131098 q = 1) : d2145 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10340 q = 1) (hb : d131098 q = 1) : d2146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10340, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10340, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10341 q = 1) (hb : d131098 q = 1) : d2147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10341, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10341, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10343 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10344 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10344, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10344, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10345 q = 1) (hb : d131098 q = 1) : d10345 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10346 q = 1) (hb : d131098 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10346, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10346, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10347 q = 1) (hb : d131098 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10347, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10347, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10348 q = 1) (hb : d131098 q = 1) : d17227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10348, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10348, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10356 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10357 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10358 q = 1) (hb : d131098 q = 1) : d17228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10358, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10358, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10359 q = 1) (hb : d131098 q = 1) : d17229 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10359, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10359, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23847 (p : Pattern) (ha : d10377 p = 1) (hb : d131098 p = 1) : d17157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10360 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10360, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10360, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2036 q = 1) (hb : d131098 q = 1) : d2036 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10361 q = 1) (hb : d131098 q = 1) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10361, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10361, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10362 q = 1) (hb : d131098 q = 1) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10362, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10362, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10364 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10365 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10365, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10365, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10366 q = 1) (hb : d131098 q = 1) : d10366 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10367 q = 1) (hb : d131098 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10367, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10367, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10368 q = 1) (hb : d131098 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10368, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10368, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10369 q = 1) (hb : d131098 q = 1) : d17155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10369, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10369, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10356 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10357 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10372 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10374 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10375 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10376 q = 1) (hb : d131098 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10376, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10377 q = 1) (hb : d131098 q = 1) : d17157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10377, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10377, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro23848 (p : Pattern) (ha : d10382 p = 1) (hb : d131098 p = 1) : d17233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10354 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10356 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10356, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10357 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10357, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10372 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10374 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10374, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10375 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10375, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10376 q = 1) (hb : d131098 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10376, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10381 q = 1) (hb : d131098 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10381, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10382 q = 1) (hb : d131098 q = 1) : d17233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10382, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10382, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23849 (p : Pattern) (ha : d10418 p = 1) (hb : d131098 p = 1) : d15558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10401 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10401, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10401, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5248 q = 1) (hb : d131098 q = 1) : d5248 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10402 q = 1) (hb : d131098 q = 1) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10402, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10402, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10403 q = 1) (hb : d131098 q = 1) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10403, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10403, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10404 q = 1) (hb : d131098 q = 1) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10404, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10404, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10414 q = 1) (hb : d131098 q = 1) : d10414 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10415 q = 1) (hb : d131098 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10415, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10416 q = 1) (hb : d131098 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10416, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10417 q = 1) (hb : d131098 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10417, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10418 q = 1) (hb : d131098 q = 1) : d15558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10418, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10418, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23850 (p : Pattern) (ha : d10424 p = 1) (hb : d131099 p = 1) : d132286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10378 q = 1) (hb : d131098 q = 1) : d17230 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23846 q ha hb
    | true =>
      simp only [d10378, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10379 q = 1) (hb : d131099 q = 1) : d19520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d131099, d19520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10379, d131099, d19520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10380 q = 1) (hb : d131099 q = 1) : d19521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d19521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, d19521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10383 q = 1) (hb : d131098 q = 1) : d17234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
    | true =>
      simp only [d10383, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23848 q ha hb
  have h6 (q : Pattern) (ha : d10384 q = 1) (hb : d131099 q = 1) : d19522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d131099, d19522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10384, d131099, d19522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10385 q = 1) (hb : d131099 q = 1) : d19523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d19523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, d19523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10386 q = 1) (hb : d131099 q = 1) : d19524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d19524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10386, d19524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10398 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
    | true =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
  have h10 (q : Pattern) (ha : d10399 q = 1) (hb : d131099 q = 1) : d19525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10400 q = 1) (hb : d131099 q = 1) : d19526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10419 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23849 q ha hb
  have h13 (q : Pattern) (ha : d10420 q = 1) (hb : d131099 q = 1) : d19527 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d10421 q = 1) (hb : d131099 q = 1) : d19528 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10422 q = 1) (hb : d131099 q = 1) : d19529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10423 q = 1) (hb : d131099 q = 1) : d19530 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d19530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10423, d19530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10424 q = 1) (hb : d131099 q = 1) : d132286 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10424, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10424, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23851 (p : Pattern) (ha : d10429 p = 1) (hb : d131099 p = 1) : d132289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
    | true =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d131099 q = 1) : d19525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d131099 q = 1) : d19526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23849 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d131099 q = 1) : d19527 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d131099 q = 1) : d19528 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d131099 q = 1) : d19529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10427 q = 1) (hb : d131099 q = 1) : d19536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d19536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10427, d19536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10428 q = 1) (hb : d131099 q = 1) : d19537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d19537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10428, d19537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10429 q = 1) (hb : d131099 q = 1) : d132289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10429, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10429, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23852 (p : Pattern) (ha : d10435 p = 1) (hb : d131099 p = 1) : d132295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10425 q = 1) (hb : d131099 q = 1) : d132287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10425, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23850 q ha hb
    | true =>
      simp only [d10425, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10426 q = 1) (hb : d131099 q = 1) : d132288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10426, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10426, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10430 q = 1) (hb : d131099 q = 1) : d132290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23851 q ha hb
    | true =>
      simp only [d10430, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10431 q = 1) (hb : d131099 q = 1) : d132291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10432 q = 1) (hb : d131099 q = 1) : d132292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10432, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10432, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10433 q = 1) (hb : d131099 q = 1) : d132293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10433, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10433, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10434 q = 1) (hb : d131099 q = 1) : d132294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10434, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10434, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10435 q = 1) (hb : d131099 q = 1) : d132295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10435, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10435, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23853 (p : Pattern) (ha : d10452 p = 1) (hb : d131099 p = 1) : d132302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10430 q = 1) (hb : d131099 q = 1) : d132290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23851 q ha hb
    | true =>
      simp only [d10430, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10431 q = 1) (hb : d131099 q = 1) : d132291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23843 q ha hb
    | true =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10449 q = 1) (hb : d131099 q = 1) : d132299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10449, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10449, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10450 q = 1) (hb : d131099 q = 1) : d132300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10450, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10450, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10451 q = 1) (hb : d131099 q = 1) : d132301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10451, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10451, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10452 q = 1) (hb : d131099 q = 1) : d132302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10452, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10452, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23854 (p : Pattern) (ha : d10559 p = 1) (hb : d131098 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d131098 q = 1) : d2066 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10437 q = 1) (hb : d131098 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10437, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d131098 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10438, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d131098 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10559 q = 1) (hb : d131098 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10559, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10559, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro23855 (p : Pattern) (ha : d10565 p = 1) (hb : d131099 p = 1) : d132305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
    | true =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d131099 q = 1) : d19525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d131099 q = 1) : d19526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23849 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d131099 q = 1) : d19527 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d131099 q = 1) : d19528 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d131099 q = 1) : d19529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10560 q = 1) (hb : d131098 q = 1) : d17294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10560, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23854 q ha hb
  have h10 (q : Pattern) (ha : d10561 q = 1) (hb : d131099 q = 1) : d19650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d131099, d19650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10561, d131099, d19650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10562 q = 1) (hb : d131099 q = 1) : d19651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d19651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, d19651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10563 q = 1) (hb : d131099 q = 1) : d19652 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d19652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10563, d19652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10564 q = 1) (hb : d131099 q = 1) : d19653 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d19653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10564, d19653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10565 q = 1) (hb : d131099 q = 1) : d132305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10565, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10565, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23856 (p : Pattern) (ha : d10571 p = 1) (hb : d131099 p = 1) : d132311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10566 q = 1) (hb : d131099 q = 1) : d132306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10566, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23855 q ha hb
    | true =>
      simp only [d10566, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10567 q = 1) (hb : d131099 q = 1) : d132307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10567, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10567, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10568 q = 1) (hb : d131099 q = 1) : d132308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10568, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10568, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10569 q = 1) (hb : d131099 q = 1) : d132309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10569, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10569, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10570 q = 1) (hb : d131099 q = 1) : d132310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10570, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10570, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10571 q = 1) (hb : d131099 q = 1) : d132311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10571, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10571, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23857 (p : Pattern) (ha : d101990 p = 1) (hb : d131099 p = 1) : d132317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10453 q = 1) (hb : d131099 q = 1) : d132303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10453, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23852 q ha hb
    | true =>
      simp only [d10453, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23853 q ha hb
  have h2 (q : Pattern) (ha : d101986 q = 1) (hb : d131099 q = 1) : d132304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101986, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10572 q = 1) (hb : d131099 q = 1) : d132312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10572, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23856 q ha hb
    | true =>
      simp only [d10572, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10573 q = 1) (hb : d131099 q = 1) : d132313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10573, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10573, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101987 q = 1) (hb : d131099 q = 1) : d132314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101987, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101988 q = 1) (hb : d131099 q = 1) : d132315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101988, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101989 q = 1) (hb : d131099 q = 1) : d132316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101989, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101990 q = 1) (hb : d131099 q = 1) : d132317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101990, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23858 (p : Pattern) (ha : d101996 p = 1) (hb : d131099 p = 1) : d132334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101991 q = 1) (hb : d131099 q = 1) : d132318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101991, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23857 q ha hb
  have h2 (q : Pattern) (ha : d10589 q = 1) (hb : d131099 q = 1) : d132329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10589, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10589, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23845 q ha hb
  have h3 (q : Pattern) (ha : d101992 q = 1) (hb : d131099 q = 1) : d132330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101993 q = 1) (hb : d131099 q = 1) : d132331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101994 q = 1) (hb : d131099 q = 1) : d132332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101995 q = 1) (hb : d131099 q = 1) : d132333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101996 q = 1) (hb : d131099 q = 1) : d132334 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101996, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23859 (p : Pattern) (ha : d102002 p = 1) (hb : d131099 p = 1) : d132340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101997 q = 1) (hb : d131099 q = 1) : d132335 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101997, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23858 q ha hb
  have h2 (q : Pattern) (ha : d101998 q = 1) (hb : d131099 q = 1) : d132336 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101998, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101999 q = 1) (hb : d131099 q = 1) : d132337 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101999, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102000 q = 1) (hb : d131099 q = 1) : d132338 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102000, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102001 q = 1) (hb : d131099 q = 1) : d132339 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102001, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102002 q = 1) (hb : d131099 q = 1) : d132340 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102002, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23860 (p : Pattern) (ha : d102008 p = 1) (hb : d131099 p = 1) : d132346 p = 1 := by
  have h0 (q : Pattern) (ha : d101925 q = 1) (hb : d131099 q = 1) : d132114 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23773 q ha hb
    | true =>
      simp only [d101925, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23786 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101943 q = 1) (hb : d131099 q = 1) : d132167 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101943, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23802 q ha hb
  have h3 (q : Pattern) (ha : d101944 q = 1) (hb : d131099 q = 1) : d132168 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101962 q = 1) (hb : d131099 q = 1) : d132224 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101962, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23821 q ha hb
  have h5 (q : Pattern) (ha : d101963 q = 1) (hb : d131099 q = 1) : d132225 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101963, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101964 q = 1) (hb : d131099 q = 1) : d132226 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101982 q = 1) (hb : d131099 q = 1) : d132282 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101982, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23840 q ha hb
  have h8 (q : Pattern) (ha : d101983 q = 1) (hb : d131099 q = 1) : d132283 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101983, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101984 q = 1) (hb : d131099 q = 1) : d132284 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101984, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101985 q = 1) (hb : d131099 q = 1) : d132285 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102003 q = 1) (hb : d131099 q = 1) : d132341 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102003, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23859 q ha hb
  have h12 (q : Pattern) (ha : d102004 q = 1) (hb : d131099 q = 1) : d132342 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102004, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102005 q = 1) (hb : d131099 q = 1) : d132343 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102005, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102006 q = 1) (hb : d131099 q = 1) : d132344 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102006, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102007 q = 1) (hb : d131099 q = 1) : d132345 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102008 q = 1) (hb : d131099 q = 1) : d132346 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23861 (p : Pattern) (ha : d102014 p = 1) (hb : d131099 p = 1) : d132352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102009 q = 1) (hb : d131099 q = 1) : d132347 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23860 q ha hb
    | true =>
      simp only [d102009, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102010 q = 1) (hb : d131099 q = 1) : d132348 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102011 q = 1) (hb : d131099 q = 1) : d132349 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102012 q = 1) (hb : d131099 q = 1) : d132350 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102013 q = 1) (hb : d131099 q = 1) : d132351 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102014 q = 1) (hb : d131099 q = 1) : d132352 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23862 (p : Pattern) (ha : d102020 p = 1) (hb : d131099 p = 1) : d132358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102015 q = 1) (hb : d131099 q = 1) : d132353 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23861 q ha hb
    | true =>
      simp only [d102015, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102016 q = 1) (hb : d131099 q = 1) : d132354 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102017 q = 1) (hb : d131099 q = 1) : d132355 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102018 q = 1) (hb : d131099 q = 1) : d132356 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102019 q = 1) (hb : d131099 q = 1) : d132357 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102020 q = 1) (hb : d131099 q = 1) : d132358 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23863 (p : Pattern) (ha : d102026 p = 1) (hb : d131099 p = 1) : d132364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102021 q = 1) (hb : d131099 q = 1) : d132359 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23862 q ha hb
    | true =>
      simp only [d102021, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102022 q = 1) (hb : d131099 q = 1) : d132360 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102023 q = 1) (hb : d131099 q = 1) : d132361 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102024 q = 1) (hb : d131099 q = 1) : d132362 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102025 q = 1) (hb : d131099 q = 1) : d132363 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102025, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102026 q = 1) (hb : d131099 q = 1) : d132364 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102026, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23864 (p : Pattern) (ha : d102032 p = 1) (hb : d131099 p = 1) : d132370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102027 q = 1) (hb : d131099 q = 1) : d132365 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23863 q ha hb
    | true =>
      simp only [d102027, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102028 q = 1) (hb : d131099 q = 1) : d132366 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102029 q = 1) (hb : d131099 q = 1) : d132367 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102030 q = 1) (hb : d131099 q = 1) : d132368 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102031 q = 1) (hb : d131099 q = 1) : d132369 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102032 q = 1) (hb : d131099 q = 1) : d132370 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23865 (p : Pattern) (ha : d102038 p = 1) (hb : d131099 p = 1) : d132376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d131099 q = 1) : d132371 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23864 q ha hb
    | true =>
      simp only [d102033, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102034 q = 1) (hb : d131099 q = 1) : d132372 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102035 q = 1) (hb : d131099 q = 1) : d132373 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102036 q = 1) (hb : d131099 q = 1) : d132374 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102037 q = 1) (hb : d131099 q = 1) : d132375 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102038 q = 1) (hb : d131099 q = 1) : d132376 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23866 (p : Pattern) (ha : d102044 p = 1) (hb : d131099 p = 1) : d132382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d131099 q = 1) : d132377 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23865 q ha hb
    | true =>
      simp only [d102039, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d131099 q = 1) : d132378 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d131099 q = 1) : d132379 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d131099 q = 1) : d132380 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d131099 q = 1) : d132381 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d131099 q = 1) : d132382 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23867 (p : Pattern) (ha : d102050 p = 1) (hb : d131099 p = 1) : d132388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d131099 q = 1) : d132383 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23866 q ha hb
    | true =>
      simp only [d102045, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d131099 q = 1) : d132384 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d131099 q = 1) : d132385 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d131099 q = 1) : d132386 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d131099 q = 1) : d132387 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d131099 q = 1) : d132388 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23868 (p : Pattern) (ha : d131114 p = 1) (hb : d131978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131109 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18544 q = 1) (hb : d131110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18545 q = 1) (hb : d131111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18546 q = 1) (hb : d131112 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d131112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18546, d131112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d18547 q = 1) (hb : d131113 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18547, d131113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18547, d131113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131114 q = 1) (hb : d131978 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131114, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131114, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23869 (p : Pattern) (ha : d131120 p = 1) (hb : d131984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131115 q = 1) (hb : d131979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131115, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23868 q ha hb
    | true =>
      simp only [d131115, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131116 q = 1) (hb : d131980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131116, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131116, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131117 q = 1) (hb : d131981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131117, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131117, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131118 q = 1) (hb : d131982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131118, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131118, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131119 q = 1) (hb : d131983 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131119, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131119, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131120 q = 1) (hb : d131984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131120, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131120, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23870 (p : Pattern) (ha : d131126 p = 1) (hb : d131990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131121 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
    | true =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131122 q = 1) (hb : d131986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131122, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131122, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131123 q = 1) (hb : d131987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131123, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131123, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131124 q = 1) (hb : d131988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131124, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131124, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131125 q = 1) (hb : d131989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131125, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131125, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131126 q = 1) (hb : d131990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131126, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131126, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23871 (p : Pattern) (ha : d131132 p = 1) (hb : d131996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131127 q = 1) (hb : d131991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131127, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131127, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23870 q ha hb
  have h2 (q : Pattern) (ha : d131128 q = 1) (hb : d131992 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131128, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131128, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131129 q = 1) (hb : d131993 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131129, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131129, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131130 q = 1) (hb : d131994 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131130, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131130, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131131 q = 1) (hb : d131995 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131131, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131131, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131132 q = 1) (hb : d131996 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131132, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131132, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23872 (p : Pattern) (ha : d131151 p = 1) (hb : d132001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h3 (q : Pattern) (ha : d18581 q = 1) (hb : d131147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18582 q = 1) (hb : d131148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d18544 q = 1) (hb : d131110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18545 q = 1) (hb : d131111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18583 q = 1) (hb : d131149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d131149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18583, d131149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18546 q = 1) (hb : d131112 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d131112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18546, d131112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d18584 q = 1) (hb : d131150 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18584, d131150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18584, d131150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131151 q = 1) (hb : d132001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131151, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131151, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23873 (p : Pattern) (ha : d131157 p = 1) (hb : d132007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131152 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23872 q ha hb
    | true =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131153 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131115 q = 1) (hb : d131979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131115, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23868 q ha hb
    | true =>
      simp only [d131115, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131116 q = 1) (hb : d131980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131116, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131116, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131154 q = 1) (hb : d132004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131154, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131154, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131155 q = 1) (hb : d132005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131155, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131155, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131156 q = 1) (hb : d132006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131156, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131156, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131157 q = 1) (hb : d132007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131157, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131157, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23874 (p : Pattern) (ha : d131163 p = 1) (hb : d132013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131158 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131158, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23873 q ha hb
    | true =>
      simp only [d131158, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131159 q = 1) (hb : d132009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131159, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131159, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131121 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
    | true =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131122 q = 1) (hb : d131986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131122, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131122, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131160 q = 1) (hb : d132010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131160, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131160, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131161 q = 1) (hb : d132011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131161, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131161, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131162 q = 1) (hb : d132012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131162, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131162, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131163 q = 1) (hb : d132013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131163, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131163, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23875 (p : Pattern) (ha : d131169 p = 1) (hb : d132019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131164 q = 1) (hb : d132014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131164, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131164, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23874 q ha hb
  have h2 (q : Pattern) (ha : d131165 q = 1) (hb : d132015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131165, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131165, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131166 q = 1) (hb : d132016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131166, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131166, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131167 q = 1) (hb : d132017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131167, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131167, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131168 q = 1) (hb : d132018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131168, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131168, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131169 q = 1) (hb : d132019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131169, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131169, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23876 (p : Pattern) (ha : d15966 p = 1) (hb : d126874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12495 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15966 q = 1) (hb : d126874 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23877 (p : Pattern) (ha : d131193 p = 1) (hb : d132025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15967 q = 1) (hb : d126875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23876 q ha hb
    | true =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h3 (q : Pattern) (ha : d18645 q = 1) (hb : d131189 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18646 q = 1) (hb : d131190 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h6 (q : Pattern) (ha : d18581 q = 1) (hb : d131147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18582 q = 1) (hb : d131148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18647 q = 1) (hb : d131191 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d18544 q = 1) (hb : d131110 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18544, d131110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d18545 q = 1) (hb : d131111 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18545, d131111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18583 q = 1) (hb : d131149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d131149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18583, d131149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18648 q = 1) (hb : d131192 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18648, d131192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18648, d131192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131193 q = 1) (hb : d132025 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131193, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131193, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23878 (p : Pattern) (ha : d131199 p = 1) (hb : d132031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131194 q = 1) (hb : d132026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131194, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23877 q ha hb
    | true =>
      simp only [d131194, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131195 q = 1) (hb : d132027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131195, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131195, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131152 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23872 q ha hb
    | true =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131153 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131196 q = 1) (hb : d132028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131196, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131196, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131197 q = 1) (hb : d132029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131197, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131197, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131198 q = 1) (hb : d132030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131198, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131198, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131199 q = 1) (hb : d132031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131199, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131199, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23879 (p : Pattern) (ha : d131205 p = 1) (hb : d132037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131152 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23872 q ha hb
    | true =>
      simp only [d131152, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131153 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131202 q = 1) (hb : d132034 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131202, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131202, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131203 q = 1) (hb : d132035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131203, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131203, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131204 q = 1) (hb : d132036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131204, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131204, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131205 q = 1) (hb : d132037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131205, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131205, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23880 (p : Pattern) (ha : d131211 p = 1) (hb : d132043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131200 q = 1) (hb : d132032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131200, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23878 q ha hb
    | true =>
      simp only [d131200, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23873 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131201 q = 1) (hb : d132033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131201, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131201, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131206 q = 1) (hb : d132038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131206, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23879 q ha hb
    | true =>
      simp only [d131206, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131207 q = 1) (hb : d132039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131207, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131207, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131208 q = 1) (hb : d132040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131208, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131208, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131209 q = 1) (hb : d132041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131209, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131209, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131210 q = 1) (hb : d132042 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131210, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131210, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131211 q = 1) (hb : d132043 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131211, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131211, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23881 (p : Pattern) (ha : d131217 p = 1) (hb : d132049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131121 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
    | true =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131213 q = 1) (hb : d132045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131213, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131213, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131214 q = 1) (hb : d132046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131214, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131214, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131215 q = 1) (hb : d132047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131215, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131215, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131216 q = 1) (hb : d132048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131216, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131216, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131217 q = 1) (hb : d132049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131217, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131217, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23882 (p : Pattern) (ha : d131223 p = 1) (hb : d132055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131212 q = 1) (hb : d132044 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131212, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131212, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23880 q ha hb
  have h2 (q : Pattern) (ha : d131218 q = 1) (hb : d132050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131218, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131218, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23881 q ha hb
  have h3 (q : Pattern) (ha : d131219 q = 1) (hb : d132051 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131219, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131219, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131220 q = 1) (hb : d132052 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131220, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131220, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131221 q = 1) (hb : d132053 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131221, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131221, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131222 q = 1) (hb : d132054 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131222, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131222, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131223 q = 1) (hb : d132055 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131223, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131223, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23883 (p : Pattern) (ha : d131229 p = 1) (hb : d132061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131133 q = 1) (hb : d131997 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131133, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131133, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23871 q ha hb
  have h2 (q : Pattern) (ha : d131134 q = 1) (hb : d131998 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131134, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131134, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131135 q = 1) (hb : d131999 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131135, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131135, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131136 q = 1) (hb : d132000 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131136, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131136, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131170 q = 1) (hb : d132020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131170, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131170, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23875 q ha hb
  have h6 (q : Pattern) (ha : d131171 q = 1) (hb : d132021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131171, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131171, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131172 q = 1) (hb : d132022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131172, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131172, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131173 q = 1) (hb : d132023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131173, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131173, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131174 q = 1) (hb : d132024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131174, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131174, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131224 q = 1) (hb : d132056 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131224, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131224, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23882 q ha hb
  have h11 (q : Pattern) (ha : d131225 q = 1) (hb : d132057 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131225, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131225, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131226 q = 1) (hb : d132058 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131226, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131226, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131227 q = 1) (hb : d132059 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131227, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131227, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131228 q = 1) (hb : d132060 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131228, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131228, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131229 q = 1) (hb : d132061 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131229, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131229, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23884 (p : Pattern) (ha : d16077 p = 1) (hb : d126985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d126981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d126982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d126982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d126982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d126983 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d126983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d126983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16076 q = 1) (hb : d126984 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d126984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16076, d126984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16077 q = 1) (hb : d126985 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d126985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16077, d126985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23885 (p : Pattern) (ha : d16081 p = 1) (hb : d126989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12495 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16081 q = 1) (hb : d126989 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d126989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16081, d126989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23886 (p : Pattern) (ha : d131257 p = 1) (hb : d132062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16078 q = 1) (hb : d126986 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d126986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23884 q ha hb
    | true =>
      simp only [d16078, d126986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23876 q ha hb
  have h3 (q : Pattern) (ha : d18729 q = 1) (hb : d131251 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18729, d131251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18729, d131251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18730 q = 1) (hb : d131252 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18730, d131252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18730, d131252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16082 q = 1) (hb : d126990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d126990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23876 q ha hb
    | true =>
      simp only [d16082, d126990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23885 q ha hb
  have h6 (q : Pattern) (ha : d18731 q = 1) (hb : d131253 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18731, d131253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18731, d131253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18732 q = 1) (hb : d131254 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18732, d131254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18732, d131254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18733 q = 1) (hb : d131255 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18733, d131255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18733, d131255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15967 q = 1) (hb : d126875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23876 q ha hb
    | true =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h10 (q : Pattern) (ha : d18645 q = 1) (hb : d131189 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d18646 q = 1) (hb : d131190 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h13 (q : Pattern) (ha : d18581 q = 1) (hb : d131147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d18582 q = 1) (hb : d131148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18647 q = 1) (hb : d131191 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18734 q = 1) (hb : d131256 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18734, d131256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18734, d131256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d131257 q = 1) (hb : d132062 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131257, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131257, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro23887 (p : Pattern) (ha : d131264 p = 1) (hb : d132065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131261 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15967 q = 1) (hb : d126875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23876 q ha hb
    | true =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h3 (q : Pattern) (ha : d18645 q = 1) (hb : d131189 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18645, d131189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18646 q = 1) (hb : d131190 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18646, d131190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h6 (q : Pattern) (ha : d18581 q = 1) (hb : d131147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18582 q = 1) (hb : d131148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18647 q = 1) (hb : d131191 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18647, d131191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18740 q = 1) (hb : d131262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d131262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18740, d131262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d18741 q = 1) (hb : d131263 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18741, d131263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18741, d131263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131264 q = 1) (hb : d132065 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131264, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131264, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23888 (p : Pattern) (ha : d131270 p = 1) (hb : d132071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131258 q = 1) (hb : d132063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131258, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23886 q ha hb
    | true =>
      simp only [d131258, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131259 q = 1) (hb : d132064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131259, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131259, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131265 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23887 q ha hb
    | true =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131266 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131267 q = 1) (hb : d132068 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131267, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131267, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131268 q = 1) (hb : d132069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131268, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131268, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131269 q = 1) (hb : d132070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131269, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131269, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131270 q = 1) (hb : d132071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131270, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131270, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23889 (p : Pattern) (ha : d131273 p = 1) (hb : d132072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h3 (q : Pattern) (ha : d18581 q = 1) (hb : d131147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18581, d131147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18582 q = 1) (hb : d131148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18582, d131148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18740 q = 1) (hb : d131262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d131262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18740, d131262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d18750 q = 1) (hb : d131272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18750, d131272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18750, d131272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131273 q = 1) (hb : d132072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131273, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131273, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23890 (p : Pattern) (ha : d131279 p = 1) (hb : d132078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131265 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23887 q ha hb
    | true =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131266 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131274 q = 1) (hb : d132073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131274, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23889 q ha hb
    | true =>
      simp only [d131274, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131275 q = 1) (hb : d132074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131275, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131275, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131276 q = 1) (hb : d132075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131276, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131276, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131277 q = 1) (hb : d132076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131277, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131277, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131278 q = 1) (hb : d132077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131278, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131278, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131279 q = 1) (hb : d132078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131279, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131279, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23891 (p : Pattern) (ha : d131290 p = 1) (hb : d132084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131265 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23887 q ha hb
    | true =>
      simp only [d131265, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131266 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131287 q = 1) (hb : d132081 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131287, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131287, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131288 q = 1) (hb : d132082 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131288, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131288, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131289 q = 1) (hb : d132083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131289, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131289, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131290 q = 1) (hb : d132084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131290, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131290, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23892 (p : Pattern) (ha : d131296 p = 1) (hb : d132090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131280 q = 1) (hb : d132079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131280, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23888 q ha hb
    | true =>
      simp only [d131280, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23890 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131286 q = 1) (hb : d132080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131286, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131286, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131291 q = 1) (hb : d132085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131291, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23891 q ha hb
    | true =>
      simp only [d131291, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131292 q = 1) (hb : d132086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131292, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131292, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131293 q = 1) (hb : d132087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131293, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131293, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131294 q = 1) (hb : d132088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131294, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131294, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131295 q = 1) (hb : d132089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131295, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131295, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131296 q = 1) (hb : d132090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131296, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131296, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23893 (p : Pattern) (ha : d131284 p = 1) (hb : d132095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131274 q = 1) (hb : d132073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131274, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23889 q ha hb
    | true =>
      simp only [d131274, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131275 q = 1) (hb : d132074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131275, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131275, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131281 q = 1) (hb : d132092 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131281, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131281, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131282 q = 1) (hb : d132093 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131282, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131282, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131283 q = 1) (hb : d132094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131283, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131283, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131284 q = 1) (hb : d132095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131284, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131284, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23894 (p : Pattern) (ha : d131303 p = 1) (hb : d132101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131298 q = 1) (hb : d132096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131298, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23893 q ha hb
    | true =>
      simp only [d131298, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131299 q = 1) (hb : d132097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131299, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131299, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131300 q = 1) (hb : d132098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131300, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131300, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131301 q = 1) (hb : d132099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131301, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131301, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131302 q = 1) (hb : d132100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131302, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131302, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131303 q = 1) (hb : d132101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131303, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131303, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23895 (p : Pattern) (ha : d131309 p = 1) (hb : d132107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131297 q = 1) (hb : d132091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131297, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131297, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23892 q ha hb
  have h2 (q : Pattern) (ha : d131304 q = 1) (hb : d132102 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131304, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131304, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23894 q ha hb
  have h3 (q : Pattern) (ha : d131305 q = 1) (hb : d132103 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131305, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131305, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131306 q = 1) (hb : d132104 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131306, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131306, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131307 q = 1) (hb : d132105 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131307, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131307, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131308 q = 1) (hb : d132106 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131308, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131308, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131309 q = 1) (hb : d132107 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131309, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131309, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23896 (p : Pattern) (ha : d131315 p = 1) (hb : d132113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131310 q = 1) (hb : d132108 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131310, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131310, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23895 q ha hb
  have h2 (q : Pattern) (ha : d131311 q = 1) (hb : d132109 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131311, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131311, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131312 q = 1) (hb : d132110 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131312, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131312, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131313 q = 1) (hb : d132111 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131313, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131313, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131314 q = 1) (hb : d132112 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131314, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131314, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131315 q = 1) (hb : d132113 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131315, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131315, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23897 (p : Pattern) (ha : d16227 p = 1) (hb : d127104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d126981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d126982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d126982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d126982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d126983 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d126983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d126983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12750 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16227 q = 1) (hb : d127104 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d127104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16227, d127104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23898 (p : Pattern) (ha : d16274 p = 1) (hb : d127151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9587 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d101169 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16270 q = 1) (hb : d127147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16271 q = 1) (hb : d127148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d127148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16271, d127148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16272 q = 1) (hb : d127149 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d127149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, d127149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9597 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14529 q = 1) (hb : d122766 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14530 q = 1) (hb : d122767 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16273 q = 1) (hb : d127150 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d127150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16273, d127150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16274 q = 1) (hb : d127151 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d127151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16274, d127151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23899 (p : Pattern) (ha : d16278 p = 1) (hb : d127155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16278 q = 1) (hb : d127155 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d127155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16278, d127155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23900 (p : Pattern) (ha : d131365 p = 1) (hb : d132115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131353 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16275 q = 1) (hb : d127152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d127152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23898 q ha hb
    | true =>
      simp only [d16275, d127152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23897 q ha hb
  have h3 (q : Pattern) (ha : d18868 q = 1) (hb : d131354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18868, d131354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18868, d131354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18869 q = 1) (hb : d131355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18869, d131355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18869, d131355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16279 q = 1) (hb : d127156 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d127156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23897 q ha hb
    | true =>
      simp only [d16279, d127156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23899 q ha hb
  have h6 (q : Pattern) (ha : d18870 q = 1) (hb : d131356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18870, d131356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18870, d131356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18871 q = 1) (hb : d131357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18871, d131357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18871, d131357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18872 q = 1) (hb : d131358 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18872, d131358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18872, d131358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16228 q = 1) (hb : d127105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d127105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23897 q ha hb
    | true =>
      simp only [d16228, d127105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h10 (q : Pattern) (ha : d18873 q = 1) (hb : d131359 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d131359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18873, d131359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d18874 q = 1) (hb : d131360 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d131360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18874, d131360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h13 (q : Pattern) (ha : d18875 q = 1) (hb : d131361 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d18876 q = 1) (hb : d131362 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18877 q = 1) (hb : d131363 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d131363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18877, d131363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18878 q = 1) (hb : d131364 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18878, d131364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18878, d131364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d131365 q = 1) (hb : d132115 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131365, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131365, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro23901 (p : Pattern) (ha : d131372 p = 1) (hb : d132118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16228 q = 1) (hb : d127105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d127105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23897 q ha hb
    | true =>
      simp only [d16228, d127105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h3 (q : Pattern) (ha : d18873 q = 1) (hb : d131359 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d131359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18873, d131359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18874 q = 1) (hb : d131360 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d131360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18874, d131360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h6 (q : Pattern) (ha : d18875 q = 1) (hb : d131361 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18876 q = 1) (hb : d131362 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18877 q = 1) (hb : d131363 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d131363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18877, d131363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18884 q = 1) (hb : d131370 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d131370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18884, d131370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d18885 q = 1) (hb : d131371 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18885, d131371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18885, d131371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131372 q = 1) (hb : d132118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131372, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131372, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23902 (p : Pattern) (ha : d131378 p = 1) (hb : d132124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131366 q = 1) (hb : d132116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131366, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23900 q ha hb
    | true =>
      simp only [d131366, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131367 q = 1) (hb : d132117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131367, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131367, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131373 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23901 q ha hb
    | true =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131374 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131375 q = 1) (hb : d132121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131375, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131375, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131376 q = 1) (hb : d132122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131376, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131376, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131377 q = 1) (hb : d132123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131377, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131377, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131378 q = 1) (hb : d132124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131378, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131378, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23903 (p : Pattern) (ha : d131381 p = 1) (hb : d132125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h3 (q : Pattern) (ha : d18875 q = 1) (hb : d131361 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18875, d131361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d18876 q = 1) (hb : d131362 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18876, d131362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18884 q = 1) (hb : d131370 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d131370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18884, d131370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d18894 q = 1) (hb : d131380 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18894, d131380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18894, d131380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131381 q = 1) (hb : d132125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131381, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131381, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23904 (p : Pattern) (ha : d131387 p = 1) (hb : d132131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131373 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23901 q ha hb
    | true =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131374 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131382 q = 1) (hb : d132126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131382, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23903 q ha hb
    | true =>
      simp only [d131382, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131383 q = 1) (hb : d132127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131383, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131383, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131384 q = 1) (hb : d132128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131384, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131384, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131385 q = 1) (hb : d132129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131385, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131385, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131386 q = 1) (hb : d132130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131386, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131386, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131387 q = 1) (hb : d132131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131387, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131387, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23905 (p : Pattern) (ha : d131398 p = 1) (hb : d132137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131373 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23901 q ha hb
    | true =>
      simp only [d131373, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131374 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131395 q = 1) (hb : d132134 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131395, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131395, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131396 q = 1) (hb : d132135 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131396, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131396, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131397 q = 1) (hb : d132136 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131397, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131397, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131398 q = 1) (hb : d132137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131398, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131398, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23906 (p : Pattern) (ha : d131404 p = 1) (hb : d132143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131388 q = 1) (hb : d132132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131388, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23902 q ha hb
    | true =>
      simp only [d131388, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23904 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131394 q = 1) (hb : d132133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131394, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131394, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131399 q = 1) (hb : d132138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131399, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23905 q ha hb
    | true =>
      simp only [d131399, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131400 q = 1) (hb : d132139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131400, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131400, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131401 q = 1) (hb : d132140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131401, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131401, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131402 q = 1) (hb : d132141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131402, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131402, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131403 q = 1) (hb : d132142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131403, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131403, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131404 q = 1) (hb : d132143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131404, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131404, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23907 (p : Pattern) (ha : d131392 p = 1) (hb : d132148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131382 q = 1) (hb : d132126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131382, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23903 q ha hb
    | true =>
      simp only [d131382, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131383 q = 1) (hb : d132127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131383, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131383, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131389 q = 1) (hb : d132145 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131389, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131389, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131390 q = 1) (hb : d132146 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131390, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131390, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131391 q = 1) (hb : d132147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131391, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131391, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131392 q = 1) (hb : d132148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131392, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131392, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23908 (p : Pattern) (ha : d131411 p = 1) (hb : d132154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131406 q = 1) (hb : d132149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131406, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23907 q ha hb
    | true =>
      simp only [d131406, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131407 q = 1) (hb : d132150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131407, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131407, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131408 q = 1) (hb : d132151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131408, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131408, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131409 q = 1) (hb : d132152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131409, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131409, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131410 q = 1) (hb : d132153 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131410, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131410, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131411 q = 1) (hb : d132154 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131411, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131411, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23909 (p : Pattern) (ha : d131417 p = 1) (hb : d132160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131405 q = 1) (hb : d132144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131405, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131405, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23906 q ha hb
  have h2 (q : Pattern) (ha : d131412 q = 1) (hb : d132155 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131412, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131412, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23908 q ha hb
  have h3 (q : Pattern) (ha : d131413 q = 1) (hb : d132156 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131413, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131413, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131414 q = 1) (hb : d132157 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131414, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131414, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131415 q = 1) (hb : d132158 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131415, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131415, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131416 q = 1) (hb : d132159 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131416, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131416, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131417 q = 1) (hb : d132160 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131417, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131417, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23910 (p : Pattern) (ha : d131423 p = 1) (hb : d132166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131418 q = 1) (hb : d132161 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131418, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131418, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23909 q ha hb
  have h2 (q : Pattern) (ha : d131419 q = 1) (hb : d132162 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131419, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131419, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131420 q = 1) (hb : d132163 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131420, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131420, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131421 q = 1) (hb : d132164 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131421, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131421, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131422 q = 1) (hb : d132165 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131422, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131422, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131423 q = 1) (hb : d132166 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131423, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131423, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23911 (p : Pattern) (ha : d14773 p = 1) (hb : d122944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d69110 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d69111 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14773 q = 1) (hb : d122944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d122944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14773, d122944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23912 (p : Pattern) (ha : d16442 p = 1) (hb : d127280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9789 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d101312 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16438 q = 1) (hb : d127276 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16439 q = 1) (hb : d127277 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d127277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16439, d127277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16440 q = 1) (hb : d127278 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d127278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16440, d127278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14758 q = 1) (hb : d122929 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14759 q = 1) (hb : d122930 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14763 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14764 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16441 q = 1) (hb : d127279 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d127279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16441, d127279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16442 q = 1) (hb : d127280 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d127280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16442, d127280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23913 (p : Pattern) (ha : d16443 p = 1) (hb : d127281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14763 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14764 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d14765 q = 1) (hb : d122936 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14765, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16443 q = 1) (hb : d127281 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d127281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16443, d127281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23914 (p : Pattern) (ha : d16511 p = 1) (hb : d127349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9753 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9755 q = 1) (hb : d101276 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16507 q = 1) (hb : d127345 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16508 q = 1) (hb : d127346 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d127346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16508, d127346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16509 q = 1) (hb : d127347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d127347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16509, d127347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9763 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9765 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14836 q = 1) (hb : d123007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14837 q = 1) (hb : d123008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d123008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14837, d123008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14758 q = 1) (hb : d122929 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14759 q = 1) (hb : d122930 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16510 q = 1) (hb : d127348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d127348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16510, d127348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16511 q = 1) (hb : d127349 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d127349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16511, d127349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23915 (p : Pattern) (ha : d16516 p = 1) (hb : d127354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d113352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d113353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14763 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14764 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16515 q = 1) (hb : d127353 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d127353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16515, d127353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14765 q = 1) (hb : d122936 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14765, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16516 q = 1) (hb : d127354 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d127354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16516, d127354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23916 (p : Pattern) (ha : d131502 p = 1) (hb : d132169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131490 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16512 q = 1) (hb : d127350 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d127350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23914 q ha hb
    | true =>
      simp only [d16512, d127350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
  have h3 (q : Pattern) (ha : d19056 q = 1) (hb : d131491 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19056, d131491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19056, d131491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19057 q = 1) (hb : d131492 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19057, d131492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19057, d131492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16517 q = 1) (hb : d127355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d127355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
    | true =>
      simp only [d16517, d127355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23915 q ha hb
  have h6 (q : Pattern) (ha : d19058 q = 1) (hb : d131493 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19058, d131493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19058, d131493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19059 q = 1) (hb : d131494 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19059, d131494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19059, d131494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19060 q = 1) (hb : d131495 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19060, d131495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19060, d131495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16444 q = 1) (hb : d127282 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
    | true =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
  have h10 (q : Pattern) (ha : d19061 q = 1) (hb : d131496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19062 q = 1) (hb : d131497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16447 q = 1) (hb : d127285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23911 q ha hb
  have h13 (q : Pattern) (ha : d19063 q = 1) (hb : d131498 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d19064 q = 1) (hb : d131499 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19065 q = 1) (hb : d131500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19066 q = 1) (hb : d131501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19066, d131501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19066, d131501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d131502 q = 1) (hb : d132169 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131502, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131502, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro23917 (p : Pattern) (ha : d131509 p = 1) (hb : d132172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131506 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16444 q = 1) (hb : d127282 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
    | true =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
  have h3 (q : Pattern) (ha : d19061 q = 1) (hb : d131496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19062 q = 1) (hb : d131497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d127285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23911 q ha hb
  have h6 (q : Pattern) (ha : d19063 q = 1) (hb : d131498 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19064 q = 1) (hb : d131499 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19065 q = 1) (hb : d131500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19072 q = 1) (hb : d131507 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19072, d131507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19072, d131507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d19073 q = 1) (hb : d131508 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19073, d131508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19073, d131508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131509 q = 1) (hb : d132172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131509, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131509, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23918 (p : Pattern) (ha : d131515 p = 1) (hb : d132178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131503 q = 1) (hb : d132170 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131503, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23916 q ha hb
    | true =>
      simp only [d131503, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131504 q = 1) (hb : d132171 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131504, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131504, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131510 q = 1) (hb : d132173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131510, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23917 q ha hb
    | true =>
      simp only [d131510, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131511 q = 1) (hb : d132174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131511, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131511, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131512 q = 1) (hb : d132175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131512, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131512, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131513 q = 1) (hb : d132176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131513, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131513, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131514 q = 1) (hb : d132177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131514, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131514, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131515 q = 1) (hb : d132178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131515, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131515, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23919 (p : Pattern) (ha : d14778 p = 1) (hb : d122949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14778 q = 1) (hb : d122949 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d122949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14778, d122949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23920 (p : Pattern) (ha : d131527 p = 1) (hb : d132179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16451 q = 1) (hb : d127289 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d127289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16451, d127289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23919 q ha hb
  have h3 (q : Pattern) (ha : d19088 q = 1) (hb : d131523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, d131523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19088, d131523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19089 q = 1) (hb : d131524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, d131524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19089, d131524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19090 q = 1) (hb : d131525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, d131525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19090, d131525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d19091 q = 1) (hb : d131526 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19091, d131526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19091, d131526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131527 q = 1) (hb : d132179 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131527, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131527, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23921 (p : Pattern) (ha : d131533 p = 1) (hb : d132185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131510 q = 1) (hb : d132173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131510, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23917 q ha hb
    | true =>
      simp only [d131510, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131511 q = 1) (hb : d132174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131511, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131511, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131528 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23920 q ha hb
    | true =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131529 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131530 q = 1) (hb : d132182 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131530, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131530, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131531 q = 1) (hb : d132183 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131531, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131531, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131532 q = 1) (hb : d132184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131532, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131532, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131533 q = 1) (hb : d132185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131533, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131533, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23922 (p : Pattern) (ha : d131560 p = 1) (hb : d132188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131555 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16444 q = 1) (hb : d127282 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
    | true =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
  have h3 (q : Pattern) (ha : d19061 q = 1) (hb : d131496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19062 q = 1) (hb : d131497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d127285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23911 q ha hb
  have h6 (q : Pattern) (ha : d19063 q = 1) (hb : d131498 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19064 q = 1) (hb : d131499 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19065 q = 1) (hb : d131500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16574 q = 1) (hb : d127378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d127378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16574, d127378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18634 q ha hb
  have h10 (q : Pattern) (ha : d19180 q = 1) (hb : d131556 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19180, d131556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19180, d131556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19181 q = 1) (hb : d131557 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19181, d131557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19181, d131557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19182 q = 1) (hb : d131558 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19182, d131558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19182, d131558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d19183 q = 1) (hb : d131559 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19183, d131559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19183, d131559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131560 q = 1) (hb : d132188 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131560, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131560, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23923 (p : Pattern) (ha : d131566 p = 1) (hb : d132194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131561 q = 1) (hb : d132189 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131561, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23922 q ha hb
    | true =>
      simp only [d131561, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131562 q = 1) (hb : d132190 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131562, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131562, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131563 q = 1) (hb : d132191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131563, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131563, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131564 q = 1) (hb : d132192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131564, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131564, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131565 q = 1) (hb : d132193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131565, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131565, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131566 q = 1) (hb : d132194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131566, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131566, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23924 (p : Pattern) (ha : d131572 p = 1) (hb : d132200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131534 q = 1) (hb : d132186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131534, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23918 q ha hb
    | true =>
      simp only [d131534, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23921 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131548 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131549 q = 1) (hb : d132187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131549, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131549, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131567 q = 1) (hb : d132195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131567, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23923 q ha hb
    | true =>
      simp only [d131567, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131568 q = 1) (hb : d132196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131568, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131568, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131569 q = 1) (hb : d132197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131569, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131569, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131570 q = 1) (hb : d132198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131570, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131570, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131571 q = 1) (hb : d132199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131571, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131571, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131572 q = 1) (hb : d132200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131572, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131572, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23925 (p : Pattern) (ha : d131547 p = 1) (hb : d132205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131528 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23920 q ha hb
    | true =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131529 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131544 q = 1) (hb : d132202 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131544, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131544, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131545 q = 1) (hb : d132203 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131545, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131545, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131546 q = 1) (hb : d132204 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131546, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131546, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131547 q = 1) (hb : d132205 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131547, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131547, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23926 (p : Pattern) (ha : d131579 p = 1) (hb : d132211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131574 q = 1) (hb : d132206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131574, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23925 q ha hb
    | true =>
      simp only [d131574, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131575 q = 1) (hb : d132207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131575, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131575, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131576 q = 1) (hb : d132208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131576, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131576, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131577 q = 1) (hb : d132209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131577, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131577, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131578 q = 1) (hb : d132210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131578, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131578, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131579 q = 1) (hb : d132211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131579, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131579, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23927 (p : Pattern) (ha : d131585 p = 1) (hb : d132217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131573 q = 1) (hb : d132201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131573, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131573, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23924 q ha hb
  have h2 (q : Pattern) (ha : d131580 q = 1) (hb : d132212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131580, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131580, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23926 q ha hb
  have h3 (q : Pattern) (ha : d131581 q = 1) (hb : d132213 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131581, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131581, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131582 q = 1) (hb : d132214 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131582, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131582, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131583 q = 1) (hb : d132215 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131583, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131583, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131584 q = 1) (hb : d132216 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131584, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131584, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131585 q = 1) (hb : d132217 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131585, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131585, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23928 (p : Pattern) (ha : d131591 p = 1) (hb : d132223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131586 q = 1) (hb : d132218 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131586, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131586, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23927 q ha hb
  have h2 (q : Pattern) (ha : d131587 q = 1) (hb : d132219 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131587, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131587, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131588 q = 1) (hb : d132220 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131588, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131588, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131589 q = 1) (hb : d132221 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131589, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131589, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131590 q = 1) (hb : d132222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131590, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131590, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131591 q = 1) (hb : d132223 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131591, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131591, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23929 (p : Pattern) (ha : d15166 p = 1) (hb : d123251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d69223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d69224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15166 q = 1) (hb : d123251 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d123251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15166, d123251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23930 (p : Pattern) (ha : d16791 p = 1) (hb : d127565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10074 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16787 q = 1) (hb : d127561 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16788 q = 1) (hb : d127562 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d127562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16788, d127562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16789 q = 1) (hb : d127563 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d127563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16789, d127563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15151 q = 1) (hb : d123236 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15152 q = 1) (hb : d123237 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15156 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15157 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16790 q = 1) (hb : d127564 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d127564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16790, d127564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16791 q = 1) (hb : d127565 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d127565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16791, d127565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23931 (p : Pattern) (ha : d16795 p = 1) (hb : d127569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10115 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16792 q = 1) (hb : d127566 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16793 q = 1) (hb : d127567 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d127567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16793, d127567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16794 q = 1) (hb : d127568 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d127568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16794, d127568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15156 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15157 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15158 q = 1) (hb : d123243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15158, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16795 q = 1) (hb : d127569 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d127569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16795, d127569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23932 (p : Pattern) (ha : d16863 p = 1) (hb : d127637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d127633 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d127634 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16861 q = 1) (hb : d127635 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d127635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16861, d127635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15229 q = 1) (hb : d123314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15230 q = 1) (hb : d123315 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10065 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15151 q = 1) (hb : d123236 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15152 q = 1) (hb : d123237 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16862 q = 1) (hb : d127636 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d127636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16862, d127636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16863 q = 1) (hb : d127637 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d127637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16863, d127637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23933 (p : Pattern) (ha : d16868 p = 1) (hb : d127642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d113608 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d113609 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15156 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15157 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16867 q = 1) (hb : d127641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d127641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16867, d127641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15158 q = 1) (hb : d123243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15158, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16868 q = 1) (hb : d127642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d127642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16868, d127642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23934 (p : Pattern) (ha : d131671 p = 1) (hb : d132227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131659 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16864 q = 1) (hb : d127638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d127638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23932 q ha hb
    | true =>
      simp only [d16864, d127638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
  have h3 (q : Pattern) (ha : d19288 q = 1) (hb : d131660 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19288, d131660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19288, d131660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19289 q = 1) (hb : d131661 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19289, d131661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19289, d131661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16869 q = 1) (hb : d127643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d127643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
    | true =>
      simp only [d16869, d127643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23933 q ha hb
  have h6 (q : Pattern) (ha : d19290 q = 1) (hb : d131662 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19290, d131662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19290, d131662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19291 q = 1) (hb : d131663 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19291, d131663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19291, d131663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19292 q = 1) (hb : d131664 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19292, d131664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19292, d131664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16796 q = 1) (hb : d127570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
    | true =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
  have h10 (q : Pattern) (ha : d19293 q = 1) (hb : d131665 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19294 q = 1) (hb : d131666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16799 q = 1) (hb : d127573 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23929 q ha hb
  have h13 (q : Pattern) (ha : d19295 q = 1) (hb : d131667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d19296 q = 1) (hb : d131668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19297 q = 1) (hb : d131669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19298 q = 1) (hb : d131670 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19298, d131670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19298, d131670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d131671 q = 1) (hb : d132227 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131671, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131671, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro23935 (p : Pattern) (ha : d131678 p = 1) (hb : d132230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131675 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16796 q = 1) (hb : d127570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
    | true =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
  have h3 (q : Pattern) (ha : d19293 q = 1) (hb : d131665 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19294 q = 1) (hb : d131666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d127573 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23929 q ha hb
  have h6 (q : Pattern) (ha : d19295 q = 1) (hb : d131667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19296 q = 1) (hb : d131668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19297 q = 1) (hb : d131669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19304 q = 1) (hb : d131676 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19304, d131676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19304, d131676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d19305 q = 1) (hb : d131677 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19305, d131677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19305, d131677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131678 q = 1) (hb : d132230 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131678, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131678, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23936 (p : Pattern) (ha : d131684 p = 1) (hb : d132236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131672 q = 1) (hb : d132228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131672, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23934 q ha hb
    | true =>
      simp only [d131672, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131673 q = 1) (hb : d132229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131673, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131673, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131679 q = 1) (hb : d132231 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131679, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23935 q ha hb
    | true =>
      simp only [d131679, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131680 q = 1) (hb : d132232 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131680, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131680, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131681 q = 1) (hb : d132233 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131681, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131681, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131682 q = 1) (hb : d132234 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131682, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131682, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131683 q = 1) (hb : d132235 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131683, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131683, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131684 q = 1) (hb : d132236 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131684, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131684, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23937 (p : Pattern) (ha : d15171 p = 1) (hb : d123256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15171 q = 1) (hb : d123256 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d123256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15171, d123256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23938 (p : Pattern) (ha : d131699 p = 1) (hb : d132237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131694 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16803 q = 1) (hb : d127577 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d127577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16803, d127577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23937 q ha hb
  have h3 (q : Pattern) (ha : d19323 q = 1) (hb : d131695 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, d131695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19323, d131695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19324 q = 1) (hb : d131696 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, d131696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19324, d131696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19325 q = 1) (hb : d131697 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, d131697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19325, d131697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d19326 q = 1) (hb : d131698 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19326, d131698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19326, d131698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131699 q = 1) (hb : d132237 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131699, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131699, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23939 (p : Pattern) (ha : d131705 p = 1) (hb : d132243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131679 q = 1) (hb : d132231 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131679, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23935 q ha hb
    | true =>
      simp only [d131679, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131680 q = 1) (hb : d132232 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131680, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131680, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131700 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23938 q ha hb
    | true =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131701 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131702 q = 1) (hb : d132240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131702, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131702, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131703 q = 1) (hb : d132241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131703, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131703, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131704 q = 1) (hb : d132242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131704, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131704, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131705 q = 1) (hb : d132243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131705, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131705, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23940 (p : Pattern) (ha : d131732 p = 1) (hb : d132246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131727 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16796 q = 1) (hb : d127570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
    | true =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
  have h3 (q : Pattern) (ha : d19293 q = 1) (hb : d131665 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19294 q = 1) (hb : d131666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d127573 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23929 q ha hb
  have h6 (q : Pattern) (ha : d19295 q = 1) (hb : d131667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19296 q = 1) (hb : d131668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19297 q = 1) (hb : d131669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16929 q = 1) (hb : d127666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d127666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16929, d127666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q ha hb
  have h10 (q : Pattern) (ha : d19418 q = 1) (hb : d131728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19418, d131728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19418, d131728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19419 q = 1) (hb : d131729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19419, d131729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19419, d131729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19420 q = 1) (hb : d131730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19420, d131730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19420, d131730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d19421 q = 1) (hb : d131731 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19421, d131731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19421, d131731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131732 q = 1) (hb : d132246 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131732, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131732, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23941 (p : Pattern) (ha : d131738 p = 1) (hb : d132252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131733 q = 1) (hb : d132247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131733, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23940 q ha hb
    | true =>
      simp only [d131733, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131734 q = 1) (hb : d132248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131734, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131734, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131735 q = 1) (hb : d132249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131735, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131735, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131736 q = 1) (hb : d132250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131736, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131736, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131737 q = 1) (hb : d132251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131737, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131737, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131738 q = 1) (hb : d132252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131738, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131738, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23942 (p : Pattern) (ha : d131744 p = 1) (hb : d132258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131706 q = 1) (hb : d132244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131706, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23936 q ha hb
    | true =>
      simp only [d131706, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23939 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131721 q = 1) (hb : d132245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131721, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131721, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131739 q = 1) (hb : d132253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131739, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23941 q ha hb
    | true =>
      simp only [d131739, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131740 q = 1) (hb : d132254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131740, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131740, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131741 q = 1) (hb : d132255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131741, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131741, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131742 q = 1) (hb : d132256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131742, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131742, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131743 q = 1) (hb : d132257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131743, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131743, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131744 q = 1) (hb : d132258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131744, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131744, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23943 (p : Pattern) (ha : d131719 p = 1) (hb : d132263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131700 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23938 q ha hb
    | true =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131701 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131716 q = 1) (hb : d132260 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131716, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131716, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131717 q = 1) (hb : d132261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131717, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131717, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131718 q = 1) (hb : d132262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131718, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131718, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131719 q = 1) (hb : d132263 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131719, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131719, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23944 (p : Pattern) (ha : d131751 p = 1) (hb : d132269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131746 q = 1) (hb : d132264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131746, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23943 q ha hb
    | true =>
      simp only [d131746, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131747 q = 1) (hb : d132265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131747, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131747, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131748 q = 1) (hb : d132266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131748, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131748, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131749 q = 1) (hb : d132267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131749, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131749, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131750 q = 1) (hb : d132268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131750, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131750, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131751 q = 1) (hb : d132269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131751, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131751, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23945 (p : Pattern) (ha : d131757 p = 1) (hb : d132275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131745 q = 1) (hb : d132259 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131745, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131745, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23942 q ha hb
  have h2 (q : Pattern) (ha : d131752 q = 1) (hb : d132270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131752, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131752, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23944 q ha hb
  have h3 (q : Pattern) (ha : d131753 q = 1) (hb : d132271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131753, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131753, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131754 q = 1) (hb : d132272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131754, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131754, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131755 q = 1) (hb : d132273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131755, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131755, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131756 q = 1) (hb : d132274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131756, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131756, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131757 q = 1) (hb : d132275 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131757, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131757, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23946 (p : Pattern) (ha : d131763 p = 1) (hb : d132281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131758 q = 1) (hb : d132276 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131758, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131758, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23945 q ha hb
  have h2 (q : Pattern) (ha : d131759 q = 1) (hb : d132277 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131759, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131759, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131760 q = 1) (hb : d132278 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131760, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131760, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131761 q = 1) (hb : d132279 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131761, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131761, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131762 q = 1) (hb : d132280 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131762, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131762, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131763 q = 1) (hb : d132281 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131763, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131763, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23947 (p : Pattern) (ha : d15558 p = 1) (hb : d123557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5248 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5249 q = 1) (hb : d69333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d69334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15558 q = 1) (hb : d123557 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d123557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15558, d123557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23948 (p : Pattern) (ha : d17157 p = 1) (hb : d127859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d127855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17155 q = 1) (hb : d127857 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d127857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17155, d127857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15548 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15549 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17156 q = 1) (hb : d127858 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17156, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17157 q = 1) (hb : d127859 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d127859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17157, d127859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23949 (p : Pattern) (ha : d17161 p = 1) (hb : d127863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10391 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10393 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17158 q = 1) (hb : d127860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17159 q = 1) (hb : d127861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, d127861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17159, d127861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17160 q = 1) (hb : d127862 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d127862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17160, d127862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15548 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15549 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15550 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15550, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17161 q = 1) (hb : d127863 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d127863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17161, d127863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23950 (p : Pattern) (ha : d17229 p = 1) (hb : d127931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17225 q = 1) (hb : d127927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17226 q = 1) (hb : d127928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17227 q = 1) (hb : d127929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d127929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17227, d127929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17228 q = 1) (hb : d127930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d127930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17228, d127930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17229 q = 1) (hb : d127931 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d127931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17229, d127931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23951 (p : Pattern) (ha : d17233 p = 1) (hb : d127935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15548 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15549 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17156 q = 1) (hb : d127858 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17156, d127858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15550 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15550, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17233 q = 1) (hb : d127935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d127935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17233, d127935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23952 (p : Pattern) (ha : d131837 p = 1) (hb : d132286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17230 q = 1) (hb : d127932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d127932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23950 q ha hb
    | true =>
      simp only [d17230, d127932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
  have h3 (q : Pattern) (ha : d19520 q = 1) (hb : d131826 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19520, d131826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19520, d131826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19521 q = 1) (hb : d131827 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19521, d131827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19521, d131827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17234 q = 1) (hb : d127936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d127936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
    | true =>
      simp only [d17234, d127936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23951 q ha hb
  have h6 (q : Pattern) (ha : d19522 q = 1) (hb : d131828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19522, d131828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19522, d131828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19523 q = 1) (hb : d131829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19523, d131829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19523, d131829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19524 q = 1) (hb : d131830 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19524, d131830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19524, d131830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17162 q = 1) (hb : d127864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
    | true =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
  have h10 (q : Pattern) (ha : d19525 q = 1) (hb : d131831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19526 q = 1) (hb : d131832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17165 q = 1) (hb : d127867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23947 q ha hb
  have h13 (q : Pattern) (ha : d19527 q = 1) (hb : d131833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d19528 q = 1) (hb : d131834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19529 q = 1) (hb : d131835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19530 q = 1) (hb : d131836 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19530, d131836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19530, d131836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d131837 q = 1) (hb : d132286 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131837, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131837, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro23953 (p : Pattern) (ha : d131844 p = 1) (hb : d132289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17162 q = 1) (hb : d127864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
    | true =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
  have h3 (q : Pattern) (ha : d19525 q = 1) (hb : d131831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19526 q = 1) (hb : d131832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d127867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23947 q ha hb
  have h6 (q : Pattern) (ha : d19527 q = 1) (hb : d131833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19528 q = 1) (hb : d131834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19529 q = 1) (hb : d131835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19536 q = 1) (hb : d131842 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19536, d131842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19536, d131842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d19537 q = 1) (hb : d131843 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19537, d131843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19537, d131843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131844 q = 1) (hb : d132289 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131844, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131844, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro23954 (p : Pattern) (ha : d131850 p = 1) (hb : d132295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131838 q = 1) (hb : d132287 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131838, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23952 q ha hb
    | true =>
      simp only [d131838, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131839 q = 1) (hb : d132288 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131839, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131839, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131845 q = 1) (hb : d132290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131845, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23953 q ha hb
    | true =>
      simp only [d131845, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131846 q = 1) (hb : d132291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131846, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131846, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131847 q = 1) (hb : d132292 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131847, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131847, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131848 q = 1) (hb : d132293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131848, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131848, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131849 q = 1) (hb : d132294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131849, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131849, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131850 q = 1) (hb : d132295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131850, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131850, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23955 (p : Pattern) (ha : d15563 p = 1) (hb : d123562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15563 q = 1) (hb : d123562 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d123562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15563, d123562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23956 (p : Pattern) (ha : d131865 p = 1) (hb : d132296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17169 q = 1) (hb : d127871 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d127871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17169, d127871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23955 q ha hb
  have h3 (q : Pattern) (ha : d19555 q = 1) (hb : d131861 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d131861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19555, d131861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19556 q = 1) (hb : d131862 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d131862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19556, d131862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19557 q = 1) (hb : d131863 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d131863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19557, d131863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d19558 q = 1) (hb : d131864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19558, d131864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19558, d131864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d131865 q = 1) (hb : d132296 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131865, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131865, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro23957 (p : Pattern) (ha : d131871 p = 1) (hb : d132302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131845 q = 1) (hb : d132290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131845, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23953 q ha hb
    | true =>
      simp only [d131845, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131846 q = 1) (hb : d132291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131846, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131846, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131866 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23956 q ha hb
    | true =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131867 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131868 q = 1) (hb : d132299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131868, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131868, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131869 q = 1) (hb : d132300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131869, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131869, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131870 q = 1) (hb : d132301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131870, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131870, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131871 q = 1) (hb : d132302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131871, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131871, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23958 (p : Pattern) (ha : d131898 p = 1) (hb : d132305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131893 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17162 q = 1) (hb : d127864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
    | true =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
  have h3 (q : Pattern) (ha : d19525 q = 1) (hb : d131831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19526 q = 1) (hb : d131832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d127867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23947 q ha hb
  have h6 (q : Pattern) (ha : d19527 q = 1) (hb : d131833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19528 q = 1) (hb : d131834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19529 q = 1) (hb : d131835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17294 q = 1) (hb : d127959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d127959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17294, d127959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q ha hb
  have h10 (q : Pattern) (ha : d19650 q = 1) (hb : d131894 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19650, d131894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19650, d131894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19651 q = 1) (hb : d131895 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19651, d131895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19651, d131895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19652 q = 1) (hb : d131896 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19652, d131896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19652, d131896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d19653 q = 1) (hb : d131897 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19653, d131897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19653, d131897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131898 q = 1) (hb : d132305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131898, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131898, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23959 (p : Pattern) (ha : d131904 p = 1) (hb : d132311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131899 q = 1) (hb : d132306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131899, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23958 q ha hb
    | true =>
      simp only [d131899, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131900 q = 1) (hb : d132307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131900, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131900, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131901 q = 1) (hb : d132308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131901, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131901, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131902 q = 1) (hb : d132309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131902, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131902, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131903 q = 1) (hb : d132310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131903, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131903, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131904 q = 1) (hb : d132311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131904, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131904, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23960 (p : Pattern) (ha : d131910 p = 1) (hb : d132317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131872 q = 1) (hb : d132303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131872, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23954 q ha hb
    | true =>
      simp only [d131872, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23957 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131887 q = 1) (hb : d132304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131887, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131887, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131905 q = 1) (hb : d132312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131905, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23959 q ha hb
    | true =>
      simp only [d131905, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131906 q = 1) (hb : d132313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131906, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131906, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131907 q = 1) (hb : d132314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131907, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131907, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131908 q = 1) (hb : d132315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131908, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131908, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131909 q = 1) (hb : d132316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131909, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131909, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131910 q = 1) (hb : d132317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131910, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131910, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23961 (p : Pattern) (ha : d131885 p = 1) (hb : d132322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131866 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23956 q ha hb
    | true =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131867 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131882 q = 1) (hb : d132319 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131882, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131882, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131883 q = 1) (hb : d132320 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131883, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131883, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131884 q = 1) (hb : d132321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131884, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131884, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131885 q = 1) (hb : d132322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131885, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131885, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23962 (p : Pattern) (ha : d131917 p = 1) (hb : d132328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131912 q = 1) (hb : d132323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131912, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23961 q ha hb
    | true =>
      simp only [d131912, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131913 q = 1) (hb : d132324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131913, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131913, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131914 q = 1) (hb : d132325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131914, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131914, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131915 q = 1) (hb : d132326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131915, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131915, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131916 q = 1) (hb : d132327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131916, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131916, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131917 q = 1) (hb : d132328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131917, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131917, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23963 (p : Pattern) (ha : d131923 p = 1) (hb : d132334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131911 q = 1) (hb : d132318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131911, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131911, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23960 q ha hb
  have h2 (q : Pattern) (ha : d131918 q = 1) (hb : d132329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131918, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131918, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23962 q ha hb
  have h3 (q : Pattern) (ha : d131919 q = 1) (hb : d132330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131919, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131919, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131920 q = 1) (hb : d132331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131920, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131920, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131921 q = 1) (hb : d132332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131921, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131921, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131922 q = 1) (hb : d132333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131922, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131922, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131923 q = 1) (hb : d132334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131923, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131923, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23964 (p : Pattern) (ha : d131929 p = 1) (hb : d132340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131924 q = 1) (hb : d132335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131924, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131924, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23963 q ha hb
  have h2 (q : Pattern) (ha : d131925 q = 1) (hb : d132336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131925, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131925, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131926 q = 1) (hb : d132337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131926, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131926, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131927 q = 1) (hb : d132338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131927, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131927, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131928 q = 1) (hb : d132339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131928, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131928, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131929 q = 1) (hb : d132340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131929, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131929, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23965 (p : Pattern) (ha : d131935 p = 1) (hb : d132346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d131316 q = 1) (hb : d132114 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131316, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23883 q ha hb
    | true =>
      simp only [d131316, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23896 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131424 q = 1) (hb : d132167 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131424, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131424, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23910 q ha hb
  have h3 (q : Pattern) (ha : d131425 q = 1) (hb : d132168 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131425, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131425, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131592 q = 1) (hb : d132224 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131592, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131592, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23928 q ha hb
  have h5 (q : Pattern) (ha : d131593 q = 1) (hb : d132225 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131593, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131593, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131594 q = 1) (hb : d132226 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131594, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131594, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131764 q = 1) (hb : d132282 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131764, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131764, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23946 q ha hb
  have h8 (q : Pattern) (ha : d131765 q = 1) (hb : d132283 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131765, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131765, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131766 q = 1) (hb : d132284 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131766, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131766, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131767 q = 1) (hb : d132285 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131767, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131767, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131930 q = 1) (hb : d132341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131930, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131930, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23964 q ha hb
  have h12 (q : Pattern) (ha : d131931 q = 1) (hb : d132342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131931, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131931, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131932 q = 1) (hb : d132343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131932, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131932, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131933 q = 1) (hb : d132344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131933, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131933, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131934 q = 1) (hb : d132345 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131934, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131934, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131935 q = 1) (hb : d132346 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131935, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131935, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro23966 (p : Pattern) (ha : d131941 p = 1) (hb : d132352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131936 q = 1) (hb : d132347 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131936, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23965 q ha hb
    | true =>
      simp only [d131936, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131937 q = 1) (hb : d132348 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131937, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131937, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131938 q = 1) (hb : d132349 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131938, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131938, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131939 q = 1) (hb : d132350 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131939, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131939, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131940 q = 1) (hb : d132351 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131940, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131940, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131941 q = 1) (hb : d132352 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131941, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131941, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23967 (p : Pattern) (ha : d131947 p = 1) (hb : d132358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131942 q = 1) (hb : d132353 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131942, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23966 q ha hb
    | true =>
      simp only [d131942, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131943 q = 1) (hb : d132354 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131943, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131943, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131944 q = 1) (hb : d132355 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131944, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131944, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131945 q = 1) (hb : d132356 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131945, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131945, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131946 q = 1) (hb : d132357 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131946, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131946, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131947 q = 1) (hb : d132358 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131947, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131947, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23968 (p : Pattern) (ha : d131953 p = 1) (hb : d132364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131948 q = 1) (hb : d132359 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131948, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23967 q ha hb
    | true =>
      simp only [d131948, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131949 q = 1) (hb : d132360 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131949, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131949, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131950 q = 1) (hb : d132361 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131950, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131950, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131951 q = 1) (hb : d132362 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131951, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131951, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131952 q = 1) (hb : d132363 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131952, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131952, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131953 q = 1) (hb : d132364 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131953, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131953, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23969 (p : Pattern) (ha : d131959 p = 1) (hb : d132370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131954 q = 1) (hb : d132365 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131954, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23968 q ha hb
    | true =>
      simp only [d131954, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131955 q = 1) (hb : d132366 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131955, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131955, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131956 q = 1) (hb : d132367 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131956, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131956, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131957 q = 1) (hb : d132368 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131957, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131957, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131958 q = 1) (hb : d132369 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131958, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131958, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131959 q = 1) (hb : d132370 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131959, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131959, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23970 (p : Pattern) (ha : d131965 p = 1) (hb : d132376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131960 q = 1) (hb : d132371 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131960, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23969 q ha hb
    | true =>
      simp only [d131960, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131961 q = 1) (hb : d132372 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131961, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131961, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131962 q = 1) (hb : d132373 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131962, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131962, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131963 q = 1) (hb : d132374 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131963, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131963, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131964 q = 1) (hb : d132375 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131964, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131964, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131965 q = 1) (hb : d132376 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131965, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131965, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23971 (p : Pattern) (ha : d131971 p = 1) (hb : d132382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131966 q = 1) (hb : d132377 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131966, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23970 q ha hb
    | true =>
      simp only [d131966, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131967 q = 1) (hb : d132378 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131967, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131967, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131968 q = 1) (hb : d132379 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131968, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131968, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131969 q = 1) (hb : d132380 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131969, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131969, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131970 q = 1) (hb : d132381 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131970, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131970, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131971 q = 1) (hb : d132382 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131971, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131971, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23972 (p : Pattern) (ha : d131977 p = 1) (hb : d132388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131972 q = 1) (hb : d132383 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131972, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23971 q ha hb
    | true =>
      simp only [d131972, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131973 q = 1) (hb : d132384 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131973, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131973, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131974 q = 1) (hb : d132385 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131974, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131974, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131975 q = 1) (hb : d132386 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131975, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131975, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131976 q = 1) (hb : d132387 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131976, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131976, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131977 q = 1) (hb : d132388 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131977, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131977, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23973 (p : Pattern) (ha : d129477 p = 1) (hb : d131099 p = 1) : d132393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d131099 q = 1) : d132050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23766 q ha hb
  have h2 (q : Pattern) (ha : d129473 q = 1) (hb : d131099 q = 1) : d132389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129473, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129473, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129474 q = 1) (hb : d131099 q = 1) : d132390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129474, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129474, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129475 q = 1) (hb : d131099 q = 1) : d132391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129475, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129475, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129476 q = 1) (hb : d131099 q = 1) : d132392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129476, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129476, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129477 q = 1) (hb : d131099 q = 1) : d132393 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129477, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129477, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23974 (p : Pattern) (ha : d129487 p = 1) (hb : d131099 p = 1) : d132403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d131099 q = 1) : d132008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23763 q ha hb
    | true =>
      simp only [d9342, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23758 q ha hb
  have h2 (q : Pattern) (ha : d129483 q = 1) (hb : d131099 q = 1) : d132399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129483, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129483, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129484 q = 1) (hb : d131099 q = 1) : d132400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129484, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129484, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129485 q = 1) (hb : d131099 q = 1) : d132401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129485, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129485, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129486 q = 1) (hb : d131099 q = 1) : d132402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129486, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129486, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129487 q = 1) (hb : d131099 q = 1) : d132403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129487, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129487, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23975 (p : Pattern) (ha : d129493 p = 1) (hb : d131099 p = 1) : d132409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129488 q = 1) (hb : d131099 q = 1) : d132404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129488, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129488, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23974 q ha hb
  have h2 (q : Pattern) (ha : d129489 q = 1) (hb : d131099 q = 1) : d132405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129489, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129489, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129490 q = 1) (hb : d131099 q = 1) : d132406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129490, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129490, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129491 q = 1) (hb : d131099 q = 1) : d132407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129491, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129491, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129492 q = 1) (hb : d131099 q = 1) : d132408 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129492, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129492, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129493 q = 1) (hb : d131099 q = 1) : d132409 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129493, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129493, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23976 (p : Pattern) (ha : d129499 p = 1) (hb : d131099 p = 1) : d132415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129478 q = 1) (hb : d131099 q = 1) : d132394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129478, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129478, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23973 q ha hb
  have h2 (q : Pattern) (ha : d129479 q = 1) (hb : d131099 q = 1) : d132395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129479, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129479, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129480 q = 1) (hb : d131099 q = 1) : d132396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129480, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129480, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129481 q = 1) (hb : d131099 q = 1) : d132397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129481, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129481, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129482 q = 1) (hb : d131099 q = 1) : d132398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129482, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129482, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129494 q = 1) (hb : d131099 q = 1) : d132410 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129494, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129494, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23975 q ha hb
  have h7 (q : Pattern) (ha : d129495 q = 1) (hb : d131099 q = 1) : d132411 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129495, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129495, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129496 q = 1) (hb : d131099 q = 1) : d132412 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129496, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129496, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129497 q = 1) (hb : d131099 q = 1) : d132413 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129497, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129497, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129498 q = 1) (hb : d131099 q = 1) : d132414 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129498, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129498, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129499 q = 1) (hb : d131099 q = 1) : d132415 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129499, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129499, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23977 (p : Pattern) (ha : d129505 p = 1) (hb : d131099 p = 1) : d132421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129500 q = 1) (hb : d131099 q = 1) : d132416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129500, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23782 q ha hb
    | true =>
      simp only [d129500, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23775 q ha hb
  have h2 (q : Pattern) (ha : d129501 q = 1) (hb : d131099 q = 1) : d132417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129501, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129501, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129502 q = 1) (hb : d131099 q = 1) : d132418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129502, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129502, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129503 q = 1) (hb : d131099 q = 1) : d132419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129503, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129503, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129504 q = 1) (hb : d131099 q = 1) : d132420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129504, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129504, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129505 q = 1) (hb : d131099 q = 1) : d132421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129505, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129505, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23978 (p : Pattern) (ha : d129511 p = 1) (hb : d131099 p = 1) : d132427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129506 q = 1) (hb : d131099 q = 1) : d132422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129506, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129506, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23977 q ha hb
  have h2 (q : Pattern) (ha : d129507 q = 1) (hb : d131099 q = 1) : d132423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129507, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129507, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129508 q = 1) (hb : d131099 q = 1) : d132424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129508, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129508, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129509 q = 1) (hb : d131099 q = 1) : d132425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129509, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129509, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129510 q = 1) (hb : d131099 q = 1) : d132426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129510, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129510, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129511 q = 1) (hb : d131099 q = 1) : d132427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129511, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129511, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23979 (p : Pattern) (ha : d129517 p = 1) (hb : d131099 p = 1) : d132433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129512 q = 1) (hb : d131099 q = 1) : d132428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129512, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129512, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23978 q ha hb
  have h2 (q : Pattern) (ha : d129513 q = 1) (hb : d131099 q = 1) : d132429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129513, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129513, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129514 q = 1) (hb : d131099 q = 1) : d132430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129514, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129514, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129515 q = 1) (hb : d131099 q = 1) : d132431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129515, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129515, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129516 q = 1) (hb : d131099 q = 1) : d132432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129516, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129516, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129517 q = 1) (hb : d131099 q = 1) : d132433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129517, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129517, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23980 (p : Pattern) (ha : d129524 p = 1) (hb : d131099 p = 1) : d132440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129519 q = 1) (hb : d131099 q = 1) : d132435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129519, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23798 q ha hb
    | true =>
      simp only [d129519, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23790 q ha hb
  have h2 (q : Pattern) (ha : d129520 q = 1) (hb : d131099 q = 1) : d132436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129520, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129520, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129521 q = 1) (hb : d131099 q = 1) : d132437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129521, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129521, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129522 q = 1) (hb : d131099 q = 1) : d132438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129522, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129522, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129523 q = 1) (hb : d131099 q = 1) : d132439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129523, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129523, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129524 q = 1) (hb : d131099 q = 1) : d132440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129524, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129524, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23981 (p : Pattern) (ha : d129530 p = 1) (hb : d131099 p = 1) : d132446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129525 q = 1) (hb : d131099 q = 1) : d132441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129525, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129525, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23980 q ha hb
  have h2 (q : Pattern) (ha : d129526 q = 1) (hb : d131099 q = 1) : d132442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129526, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129526, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129527 q = 1) (hb : d131099 q = 1) : d132443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129527, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129527, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129528 q = 1) (hb : d131099 q = 1) : d132444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129528, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129528, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129529 q = 1) (hb : d131099 q = 1) : d132445 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129529, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129529, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129530 q = 1) (hb : d131099 q = 1) : d132446 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129530, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129530, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23982 (p : Pattern) (ha : d129536 p = 1) (hb : d131099 p = 1) : d132452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129531 q = 1) (hb : d131099 q = 1) : d132447 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129531, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129531, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23981 q ha hb
  have h2 (q : Pattern) (ha : d129532 q = 1) (hb : d131099 q = 1) : d132448 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129532, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129532, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129533 q = 1) (hb : d131099 q = 1) : d132449 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129533, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129533, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129534 q = 1) (hb : d131099 q = 1) : d132450 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129534, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129534, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129535 q = 1) (hb : d131099 q = 1) : d132451 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129535, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129535, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129536 q = 1) (hb : d131099 q = 1) : d132452 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129536, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129536, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23983 (p : Pattern) (ha : d129540 p = 1) (hb : d131099 p = 1) : d132456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23809 q ha hb
    | true =>
      simp only [d9834, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d131099 q = 1) : d19061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d131099, d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d131099 q = 1) : d19062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9851, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23811 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d131099 q = 1) : d19063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d131099, d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d131099 q = 1) : d19064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d131099 q = 1) : d19065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9870 q = 1) (hb : d131098 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23804 q ha hb
  have h10 (q : Pattern) (ha : d9871 q = 1) (hb : d131099 q = 1) : d19088 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d131099, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9871, d131099, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9872 q = 1) (hb : d131099 q = 1) : d19089 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9873 q = 1) (hb : d131099 q = 1) : d19090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129539 q = 1) (hb : d131099 q = 1) : d132455 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129539, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129539, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129540 q = 1) (hb : d131099 q = 1) : d132456 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129540, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129540, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23984 (p : Pattern) (ha : d129546 p = 1) (hb : d131099 p = 1) : d132462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129541 q = 1) (hb : d131099 q = 1) : d132457 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129541, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23983 q ha hb
    | true =>
      simp only [d129541, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129542 q = 1) (hb : d131099 q = 1) : d132458 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129542, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129542, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23805 q ha hb
    | true =>
      simp only [d9876, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129543 q = 1) (hb : d131099 q = 1) : d132459 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129543, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129543, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129544 q = 1) (hb : d131099 q = 1) : d132460 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129544, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129544, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129545 q = 1) (hb : d131099 q = 1) : d132461 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129545, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129545, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129546 q = 1) (hb : d131099 q = 1) : d132462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129546, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129546, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23985 (p : Pattern) (ha : d129552 p = 1) (hb : d131099 p = 1) : d132468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129547 q = 1) (hb : d131099 q = 1) : d132463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129547, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23984 q ha hb
    | true =>
      simp only [d129547, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23806 q ha hb
  have h2 (q : Pattern) (ha : d129548 q = 1) (hb : d131099 q = 1) : d132464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129548, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129548, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129549 q = 1) (hb : d131099 q = 1) : d132465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129549, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129549, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129550 q = 1) (hb : d131099 q = 1) : d132466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129550, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129550, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129551 q = 1) (hb : d131099 q = 1) : d132467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129551, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129551, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129552 q = 1) (hb : d131099 q = 1) : d132468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129552, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129552, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23986 (p : Pattern) (ha : d129558 p = 1) (hb : d131099 p = 1) : d132474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129553 q = 1) (hb : d131099 q = 1) : d132469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129553, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129553, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23985 q ha hb
  have h2 (q : Pattern) (ha : d129554 q = 1) (hb : d131099 q = 1) : d132470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129554, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129554, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129555 q = 1) (hb : d131099 q = 1) : d132471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129555, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129555, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129556 q = 1) (hb : d131099 q = 1) : d132472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129556, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129556, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129557 q = 1) (hb : d131099 q = 1) : d132473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129557, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129557, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129558 q = 1) (hb : d131099 q = 1) : d132474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129558, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129558, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23987 (p : Pattern) (ha : d129564 p = 1) (hb : d131099 p = 1) : d132480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129559 q = 1) (hb : d131099 q = 1) : d132475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129559, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129559, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23986 q ha hb
  have h2 (q : Pattern) (ha : d129560 q = 1) (hb : d131099 q = 1) : d132476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129560, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129560, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129561 q = 1) (hb : d131099 q = 1) : d132477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129561, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129561, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129562 q = 1) (hb : d131099 q = 1) : d132478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129562, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129562, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129563 q = 1) (hb : d131099 q = 1) : d132479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129563, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129563, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129564 q = 1) (hb : d131099 q = 1) : d132480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129564, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129564, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23988 (p : Pattern) (ha : d129569 p = 1) (hb : d131099 p = 1) : d132485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23828 q ha hb
    | true =>
      simp only [d10122, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d131099 q = 1) : d19293 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d131099, d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d131099 q = 1) : d19294 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10142, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23830 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d131099 q = 1) : d19295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d131099, d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d131099 q = 1) : d19296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d131099 q = 1) : d19297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10164 q = 1) (hb : d131098 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23822 q ha hb
    | true =>
      simp only [d10164, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23823 q ha hb
  have h10 (q : Pattern) (ha : d10165 q = 1) (hb : d131099 q = 1) : d19323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d131099, d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10165, d131099, d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10166 q = 1) (hb : d131099 q = 1) : d19324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10167 q = 1) (hb : d131099 q = 1) : d19325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10167, d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129568 q = 1) (hb : d131099 q = 1) : d132484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129568, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129568, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129569 q = 1) (hb : d131099 q = 1) : d132485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129569, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129569, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23989 (p : Pattern) (ha : d129575 p = 1) (hb : d131099 p = 1) : d132491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129570 q = 1) (hb : d131099 q = 1) : d132486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129570, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23988 q ha hb
    | true =>
      simp only [d129570, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129571 q = 1) (hb : d131099 q = 1) : d132487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129571, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129571, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23824 q ha hb
    | true =>
      simp only [d10170, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129572 q = 1) (hb : d131099 q = 1) : d132488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129572, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129572, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129573 q = 1) (hb : d131099 q = 1) : d132489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129573, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129573, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129574 q = 1) (hb : d131099 q = 1) : d132490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129574, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129574, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129575 q = 1) (hb : d131099 q = 1) : d132491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129575, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129575, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23990 (p : Pattern) (ha : d129581 p = 1) (hb : d131099 p = 1) : d132497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129576 q = 1) (hb : d131099 q = 1) : d132492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129576, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23989 q ha hb
    | true =>
      simp only [d129576, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23825 q ha hb
  have h2 (q : Pattern) (ha : d129577 q = 1) (hb : d131099 q = 1) : d132493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129577, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129577, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129578 q = 1) (hb : d131099 q = 1) : d132494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129578, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129578, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129579 q = 1) (hb : d131099 q = 1) : d132495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129579, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129579, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129580 q = 1) (hb : d131099 q = 1) : d132496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129580, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129580, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129581 q = 1) (hb : d131099 q = 1) : d132497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129581, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129581, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23991 (p : Pattern) (ha : d129587 p = 1) (hb : d131099 p = 1) : d132503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129582 q = 1) (hb : d131099 q = 1) : d132498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129582, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129582, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23990 q ha hb
  have h2 (q : Pattern) (ha : d129583 q = 1) (hb : d131099 q = 1) : d132499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129583, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129583, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129584 q = 1) (hb : d131099 q = 1) : d132500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129584, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129584, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129585 q = 1) (hb : d131099 q = 1) : d132501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129585, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129585, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129586 q = 1) (hb : d131099 q = 1) : d132502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129586, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129586, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129587 q = 1) (hb : d131099 q = 1) : d132503 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129587, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129587, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23992 (p : Pattern) (ha : d129593 p = 1) (hb : d131099 p = 1) : d132509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129588 q = 1) (hb : d131099 q = 1) : d132504 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129588, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129588, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23991 q ha hb
  have h2 (q : Pattern) (ha : d129589 q = 1) (hb : d131099 q = 1) : d132505 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129589, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129589, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129590 q = 1) (hb : d131099 q = 1) : d132506 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129590, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129590, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129591 q = 1) (hb : d131099 q = 1) : d132507 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129591, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129591, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129592 q = 1) (hb : d131099 q = 1) : d132508 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129592, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129592, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129593 q = 1) (hb : d131099 q = 1) : d132509 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129593, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129593, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23993 (p : Pattern) (ha : d129599 p = 1) (hb : d131099 p = 1) : d132515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23847 q ha hb
    | true =>
      simp only [d10398, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d131099 q = 1) : d19525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d131099, d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d131099 q = 1) : d19526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10419, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23849 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d131099 q = 1) : d19527 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d131099, d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d131099 q = 1) : d19528 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d131099 q = 1) : d19529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10441 q = 1) (hb : d131098 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23841 q ha hb
    | true =>
      simp only [d10441, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23842 q ha hb
  have h10 (q : Pattern) (ha : d10442 q = 1) (hb : d131099 q = 1) : d19555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d131099, d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10442, d131099, d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10443 q = 1) (hb : d131099 q = 1) : d19556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10444 q = 1) (hb : d131099 q = 1) : d19557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10444, d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129598 q = 1) (hb : d131099 q = 1) : d132514 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129598, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129598, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129599 q = 1) (hb : d131099 q = 1) : d132515 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129599, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129599, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23994 (p : Pattern) (ha : d129605 p = 1) (hb : d131099 p = 1) : d132521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129600 q = 1) (hb : d131099 q = 1) : d132516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129600, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23993 q ha hb
    | true =>
      simp only [d129600, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129601 q = 1) (hb : d131099 q = 1) : d132517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129601, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129601, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23843 q ha hb
    | true =>
      simp only [d10447, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129602 q = 1) (hb : d131099 q = 1) : d132518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129602, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129602, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129603 q = 1) (hb : d131099 q = 1) : d132519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129603, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129603, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129604 q = 1) (hb : d131099 q = 1) : d132520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129604, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129604, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129605 q = 1) (hb : d131099 q = 1) : d132521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129605, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129605, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23995 (p : Pattern) (ha : d129611 p = 1) (hb : d131099 p = 1) : d132527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129606 q = 1) (hb : d131099 q = 1) : d132522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129606, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23994 q ha hb
    | true =>
      simp only [d129606, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23844 q ha hb
  have h2 (q : Pattern) (ha : d129607 q = 1) (hb : d131099 q = 1) : d132523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129607, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129607, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129608 q = 1) (hb : d131099 q = 1) : d132524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129608, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129608, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129609 q = 1) (hb : d131099 q = 1) : d132525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129609, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129609, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129610 q = 1) (hb : d131099 q = 1) : d132526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129610, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129610, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129611 q = 1) (hb : d131099 q = 1) : d132527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129611, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129611, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23996 (p : Pattern) (ha : d129617 p = 1) (hb : d131099 p = 1) : d132533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129612 q = 1) (hb : d131099 q = 1) : d132528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129612, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129612, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23995 q ha hb
  have h2 (q : Pattern) (ha : d129613 q = 1) (hb : d131099 q = 1) : d132529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129613, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129613, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129614 q = 1) (hb : d131099 q = 1) : d132530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129614, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129614, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129615 q = 1) (hb : d131099 q = 1) : d132531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129615, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129615, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129616 q = 1) (hb : d131099 q = 1) : d132532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129616, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129616, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129617 q = 1) (hb : d131099 q = 1) : d132533 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129617, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129617, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23997 (p : Pattern) (ha : d129623 p = 1) (hb : d131099 p = 1) : d132539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129618 q = 1) (hb : d131099 q = 1) : d132534 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129618, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129618, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23996 q ha hb
  have h2 (q : Pattern) (ha : d129619 q = 1) (hb : d131099 q = 1) : d132535 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129619, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129619, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129620 q = 1) (hb : d131099 q = 1) : d132536 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129620, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129620, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129621 q = 1) (hb : d131099 q = 1) : d132537 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129621, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129621, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129622 q = 1) (hb : d131099 q = 1) : d132538 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129622, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129622, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129623 q = 1) (hb : d131099 q = 1) : d132539 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129623, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129623, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23998 (p : Pattern) (ha : d129629 p = 1) (hb : d131099 p = 1) : d132545 p = 1 := by
  have h0 (q : Pattern) (ha : d129518 q = 1) (hb : d131099 q = 1) : d132434 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129518, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23976 q ha hb
    | true =>
      simp only [d129518, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23979 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129537 q = 1) (hb : d131099 q = 1) : d132453 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129537, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129537, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23982 q ha hb
  have h3 (q : Pattern) (ha : d129538 q = 1) (hb : d131099 q = 1) : d132454 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129538, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129538, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129565 q = 1) (hb : d131099 q = 1) : d132481 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129565, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129565, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23987 q ha hb
  have h5 (q : Pattern) (ha : d129566 q = 1) (hb : d131099 q = 1) : d132482 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129566, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129566, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129567 q = 1) (hb : d131099 q = 1) : d132483 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129567, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129567, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129594 q = 1) (hb : d131099 q = 1) : d132510 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129594, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129594, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23992 q ha hb
  have h8 (q : Pattern) (ha : d129595 q = 1) (hb : d131099 q = 1) : d132511 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129595, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129595, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129596 q = 1) (hb : d131099 q = 1) : d132512 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129596, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129596, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129597 q = 1) (hb : d131099 q = 1) : d132513 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129597, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129597, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129624 q = 1) (hb : d131099 q = 1) : d132540 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129624, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129624, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23997 q ha hb
  have h12 (q : Pattern) (ha : d129625 q = 1) (hb : d131099 q = 1) : d132541 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129625, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129625, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129626 q = 1) (hb : d131099 q = 1) : d132542 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129626, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129626, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129627 q = 1) (hb : d131099 q = 1) : d132543 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129627, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129627, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129628 q = 1) (hb : d131099 q = 1) : d132544 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129628, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129628, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129629 q = 1) (hb : d131099 q = 1) : d132545 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129629, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129629, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23999 (p : Pattern) (ha : d129635 p = 1) (hb : d131099 p = 1) : d132551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129630 q = 1) (hb : d131099 q = 1) : d132546 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129630, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23998 q ha hb
    | true =>
      simp only [d129630, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129631 q = 1) (hb : d131099 q = 1) : d132547 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129631, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129631, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129632 q = 1) (hb : d131099 q = 1) : d132548 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129632, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129632, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129633 q = 1) (hb : d131099 q = 1) : d132549 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129633, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129633, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129634 q = 1) (hb : d131099 q = 1) : d132550 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129634, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129634, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129635 q = 1) (hb : d131099 q = 1) : d132551 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129635, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129635, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
