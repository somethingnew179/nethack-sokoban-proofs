import NetHack.Soko22Hazard87.AndIntroBlocks0102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro25750 (p : Pattern) (ha : d10691 p = 1) (hb : d112686 p = 1) : d141338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d112686 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10689 q = 1) (hb : d112686 q = 1) : d141336 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10689, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d112686 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10690 q = 1) (hb : d112686 q = 1) : d141337 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10690, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10691 q = 1) (hb : d112686 q = 1) : d141338 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10691, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro25751 (p : Pattern) (ha : d10697 p = 1) (hb : d112686 p = 1) : d141344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d112686 q = 1) : d141339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25750 q ha hb
    | true =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d112686 q = 1) : d141340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d112686 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10694 q = 1) (hb : d112686 q = 1) : d141341 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10695 q = 1) (hb : d112686 q = 1) : d141342 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10695, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10696 q = 1) (hb : d112686 q = 1) : d141343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10696, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10697 q = 1) (hb : d112686 q = 1) : d141344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10697, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25752 (p : Pattern) (ha : d108806 p = 1) (hb : d112686 p = 1) : d141350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112686 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d112686 q = 1) : d141345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25751 q ha hb
    | true =>
      simp only [d10698, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108802 q = 1) (hb : d112686 q = 1) : d141346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108802, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d112686 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108803 q = 1) (hb : d112686 q = 1) : d141347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108803, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108804 q = 1) (hb : d112686 q = 1) : d141348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108804, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108805 q = 1) (hb : d112686 q = 1) : d141349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108805, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108806 q = 1) (hb : d112686 q = 1) : d141350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108806, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25753 (p : Pattern) (ha : d108812 p = 1) (hb : d112686 p = 1) : d141356 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d112686 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108790 q = 1) (hb : d112686 q = 1) : d141324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25746 q ha hb
    | true =>
      simp only [d108790, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25748 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d112686 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108791 q = 1) (hb : d112686 q = 1) : d141325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108791, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108792 q = 1) (hb : d112686 q = 1) : d141326 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108792, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108793 q = 1) (hb : d112686 q = 1) : d141327 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108793, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108797 q = 1) (hb : d112686 q = 1) : d141331 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108797, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25749 q ha hb
  have h8 (q : Pattern) (ha : d108798 q = 1) (hb : d112686 q = 1) : d141332 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108798, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d108799 q = 1) (hb : d112686 q = 1) : d141333 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108799, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d108800 q = 1) (hb : d112686 q = 1) : d141334 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108800, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108801 q = 1) (hb : d112686 q = 1) : d141335 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108801, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108807 q = 1) (hb : d112686 q = 1) : d141351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108807, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25752 q ha hb
  have h13 (q : Pattern) (ha : d108808 q = 1) (hb : d112686 q = 1) : d141352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108808, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d108809 q = 1) (hb : d112686 q = 1) : d141353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108809, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d108810 q = 1) (hb : d112686 q = 1) : d141354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108810, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d108811 q = 1) (hb : d112686 q = 1) : d141355 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108811, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108812 q = 1) (hb : d112686 q = 1) : d141356 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108812, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25754 (p : Pattern) (ha : d10719 p = 1) (hb : d112686 p = 1) : d141366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112686 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d112686 q = 1) : d141311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
    | true =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d112686 q = 1) : d141362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d112686 q = 1) : d141363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d112686 q = 1) : d141364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d112686 q = 1) : d141365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10719 q = 1) (hb : d112686 q = 1) : d141366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25755 (p : Pattern) (ha : d10726 p = 1) (hb : d112686 p = 1) : d141373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112686 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d112686 q = 1) : d141311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
    | true =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d112686 q = 1) : d141362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d112686 q = 1) : d141363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d112686 q = 1) : d141364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d112686 q = 1) : d141365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d112686 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10668 q = 1) (hb : d112686 q = 1) : d141318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
    | true =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10722 q = 1) (hb : d112686 q = 1) : d141369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10723 q = 1) (hb : d112686 q = 1) : d141370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10723, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10724 q = 1) (hb : d112686 q = 1) : d141371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10725 q = 1) (hb : d112686 q = 1) : d141372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10726 q = 1) (hb : d112686 q = 1) : d141373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10726, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro25756 (p : Pattern) (ha : d10801 p = 1) (hb : d112686 p = 1) : d141430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112686 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d112686 q = 1) : d141311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
    | true =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d112686 q = 1) : d141362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d112686 q = 1) : d141363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d112686 q = 1) : d141364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d112686 q = 1) : d141365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d112686 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10801 q = 1) (hb : d112686 q = 1) : d141430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10801, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25757 (p : Pattern) (ha : d10731 p = 1) (hb : d112686 p = 1) : d141378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d112686 q = 1) : d141308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d112686 q = 1) : d141377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10731 q = 1) (hb : d112686 q = 1) : d141378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25758 (p : Pattern) (ha : d10738 p = 1) (hb : d112686 p = 1) : d141385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d112686 q = 1) : d141383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d112686 q = 1) : d141384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10738 q = 1) (hb : d112686 q = 1) : d141385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25759 (p : Pattern) (ha : d10747 p = 1) (hb : d112686 p = 1) : d141391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d112686 q = 1) : d141389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d112686 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10652 q = 1) (hb : d112686 q = 1) : d141302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10652, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10746 q = 1) (hb : d112686 q = 1) : d141390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10746, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10747 q = 1) (hb : d112686 q = 1) : d141391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10747, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro25760 (p : Pattern) (ha : d10753 p = 1) (hb : d112686 p = 1) : d141397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d112686 q = 1) : d141392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25759 q ha hb
    | true =>
      simp only [d10748, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d112686 q = 1) : d141393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d112686 q = 1) : d141394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d112686 q = 1) : d141395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d112686 q = 1) : d141396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d112686 q = 1) : d141397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25761 (p : Pattern) (ha : d10772 p = 1) (hb : d112686 p = 1) : d141403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d112686 q = 1) : d141400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d112686 q = 1) : d141401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d112686 q = 1) : d141402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d112686 q = 1) : d141403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25762 (p : Pattern) (ha : d108822 p = 1) (hb : d112686 p = 1) : d141409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112686 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d112686 q = 1) : d141379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25757 q ha hb
    | true =>
      simp only [d10732, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d112686 q = 1) : d141380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d112686 q = 1) : d141381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d112686 q = 1) : d141382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112686 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d112686 q = 1) : d141386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25758 q ha hb
    | true =>
      simp only [d10739, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d112686 q = 1) : d141387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d112686 q = 1) : d141388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d112686 q = 1) : d141398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25760 q ha hb
    | true =>
      simp only [d10754, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d112686 q = 1) : d141399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d112686 q = 1) : d141404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25761 q ha hb
    | true =>
      simp only [d10773, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d112686 q = 1) : d141405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d112686 q = 1) : d141406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d112686 q = 1) : d141407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d112686 q = 1) : d141408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108822 q = 1) (hb : d112686 q = 1) : d141409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25763 (p : Pattern) (ha : d10779 p = 1) (hb : d112686 p = 1) : d141410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d112686 q = 1) : d141308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d112686 q = 1) : d141377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10779 q = 1) (hb : d112686 q = 1) : d141410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10779, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25764 (p : Pattern) (ha : d10784 p = 1) (hb : d112686 p = 1) : d141415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d112686 q = 1) : d141383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d112686 q = 1) : d141384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10784 q = 1) (hb : d112686 q = 1) : d141415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10784, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25765 (p : Pattern) (ha : d10788 p = 1) (hb : d112686 p = 1) : d141419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d112686 q = 1) : d141392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25759 q ha hb
    | true =>
      simp only [d10748, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d112686 q = 1) : d141393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d112686 q = 1) : d141394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d112686 q = 1) : d141395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d112686 q = 1) : d141396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d112686 q = 1) : d141419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25766 (p : Pattern) (ha : d10793 p = 1) (hb : d112686 p = 1) : d141422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d112686 q = 1) : d141400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d112686 q = 1) : d141401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d112686 q = 1) : d141402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d112686 q = 1) : d141422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25767 (p : Pattern) (ha : d108827 p = 1) (hb : d112686 p = 1) : d141428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112686 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d112686 q = 1) : d141379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25757 q ha hb
    | true =>
      simp only [d10732, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d112686 q = 1) : d141380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d112686 q = 1) : d141381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d112686 q = 1) : d141382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112686 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d112686 q = 1) : d141386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25758 q ha hb
    | true =>
      simp only [d10739, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d112686 q = 1) : d141387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d112686 q = 1) : d141388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d112686 q = 1) : d141398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25760 q ha hb
    | true =>
      simp only [d10754, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d112686 q = 1) : d141399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d112686 q = 1) : d141404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25761 q ha hb
    | true =>
      simp only [d10773, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d112686 q = 1) : d141405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d112686 q = 1) : d141406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d112686 q = 1) : d141407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d112686 q = 1) : d141408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d112686 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10780 q = 1) (hb : d112686 q = 1) : d141411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25763 q ha hb
    | true =>
      simp only [d10780, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10781 q = 1) (hb : d112686 q = 1) : d141412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10782 q = 1) (hb : d112686 q = 1) : d141413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10782, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10783 q = 1) (hb : d112686 q = 1) : d141414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d112686 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10785 q = 1) (hb : d112686 q = 1) : d141416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25764 q ha hb
    | true =>
      simp only [d10785, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10786 q = 1) (hb : d112686 q = 1) : d141417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10787 q = 1) (hb : d112686 q = 1) : d141418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10787, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10789 q = 1) (hb : d112686 q = 1) : d141420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25765 q ha hb
    | true =>
      simp only [d10789, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
  have h27 (q : Pattern) (ha : d108823 q = 1) (hb : d112686 q = 1) : d141421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108823, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10794 q = 1) (hb : d112686 q = 1) : d141423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25766 q ha hb
    | true =>
      simp only [d10794, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10795 q = 1) (hb : d112686 q = 1) : d141424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10795, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108824 q = 1) (hb : d112686 q = 1) : d141425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108824, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108825 q = 1) (hb : d112686 q = 1) : d141426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108825, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108826 q = 1) (hb : d112686 q = 1) : d141427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108826, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108827 q = 1) (hb : d112686 q = 1) : d141428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108827, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro25768 (p : Pattern) (ha : d108834 p = 1) (hb : d112686 p = 1) : d141437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d112686 q = 1) : d141420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25765 q ha hb
    | true =>
      simp only [d10789, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
  have h2 (q : Pattern) (ha : d108823 q = 1) (hb : d112686 q = 1) : d141421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108823, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d112686 q = 1) : d141423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25766 q ha hb
    | true =>
      simp only [d10794, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d112686 q = 1) : d141424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d112686 q = 1) : d141425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d112686 q = 1) : d141435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d112686 q = 1) : d141436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d112686 q = 1) : d141437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25769 (p : Pattern) (ha : d10819 p = 1) (hb : d112686 p = 1) : d141445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d112686 q = 1) : d141443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d112686 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10689 q = 1) (hb : d112686 q = 1) : d141336 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10689, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10818 q = 1) (hb : d112686 q = 1) : d141444 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10818, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10819 q = 1) (hb : d112686 q = 1) : d141445 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10819, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro25770 (p : Pattern) (ha : d10825 p = 1) (hb : d112686 p = 1) : d141451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d112686 q = 1) : d141446 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25769 q ha hb
    | true =>
      simp only [d10820, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d112686 q = 1) : d141447 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d112686 q = 1) : d141339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25750 q ha hb
    | true =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d112686 q = 1) : d141340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d112686 q = 1) : d141448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d112686 q = 1) : d141449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d112686 q = 1) : d141450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d112686 q = 1) : d141451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25771 (p : Pattern) (ha : d10844 p = 1) (hb : d112686 p = 1) : d141457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d112686 q = 1) : d141339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25750 q ha hb
    | true =>
      simp only [d10692, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d112686 q = 1) : d141340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d112686 q = 1) : d141454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d112686 q = 1) : d141455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d112686 q = 1) : d141456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d112686 q = 1) : d141457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25772 (p : Pattern) (ha : d108844 p = 1) (hb : d112686 p = 1) : d141463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d112686 q = 1) : d141452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25770 q ha hb
    | true =>
      simp only [d10826, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25751 q ha hb
  have h2 (q : Pattern) (ha : d108840 q = 1) (hb : d112686 q = 1) : d141453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108840, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d112686 q = 1) : d141458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25771 q ha hb
    | true =>
      simp only [d10845, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d112686 q = 1) : d141459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d112686 q = 1) : d141460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d112686 q = 1) : d141461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d112686 q = 1) : d141462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d112686 q = 1) : d141463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25773 (p : Pattern) (ha : d108850 p = 1) (hb : d112686 p = 1) : d141469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d112686 q = 1) : d141367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25754 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d112686 q = 1) : d141368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d112686 q = 1) : d141374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25754 q ha hb
    | true =>
      simp only [d10727, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25755 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d112686 q = 1) : d141375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d112686 q = 1) : d141376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108828 q = 1) (hb : d112686 q = 1) : d141429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25762 q ha hb
    | true =>
      simp only [d108828, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25767 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d112686 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10802 q = 1) (hb : d112686 q = 1) : d141431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25756 q ha hb
    | true =>
      simp only [d10802, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108829 q = 1) (hb : d112686 q = 1) : d141432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108830 q = 1) (hb : d112686 q = 1) : d141433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108830, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108831 q = 1) (hb : d112686 q = 1) : d141434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108831, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108835 q = 1) (hb : d112686 q = 1) : d141438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108835, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25768 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d112686 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108836 q = 1) (hb : d112686 q = 1) : d141439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108836, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108837 q = 1) (hb : d112686 q = 1) : d141440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108837, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108838 q = 1) (hb : d112686 q = 1) : d141441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108838, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108839 q = 1) (hb : d112686 q = 1) : d141442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108839, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108845 q = 1) (hb : d112686 q = 1) : d141464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108845, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25772 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d112686 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108846 q = 1) (hb : d112686 q = 1) : d141465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108846, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108847 q = 1) (hb : d112686 q = 1) : d141466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108847, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108848 q = 1) (hb : d112686 q = 1) : d141467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108848, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108849 q = 1) (hb : d112686 q = 1) : d141468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108849, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108850 q = 1) (hb : d112686 q = 1) : d141469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108850, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro25774 (p : Pattern) (ha : d108856 p = 1) (hb : d112686 p = 1) : d141475 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d112686 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108813 q = 1) (hb : d112686 q = 1) : d141357 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108813, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25753 q ha hb
  have h3 (q : Pattern) (ha : d108814 q = 1) (hb : d112686 q = 1) : d141358 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108814, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108815 q = 1) (hb : d112686 q = 1) : d141359 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108815, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108816 q = 1) (hb : d112686 q = 1) : d141360 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108816, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108817 q = 1) (hb : d112686 q = 1) : d141361 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108817, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d112686 q = 1) : d141470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25773 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d112686 q = 1) : d141471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d112686 q = 1) : d141472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d112686 q = 1) : d141473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d112686 q = 1) : d141474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d112686 q = 1) : d141475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108856, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro25775 (p : Pattern) (ha : d10865 p = 1) (hb : d112686 p = 1) : d141477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d112686 q = 1) : d141389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10863 q = 1) (hb : d112686 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10863, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10864 q = 1) (hb : d112686 q = 1) : d141476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10864, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10865 q = 1) (hb : d112686 q = 1) : d141477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10865, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25776 (p : Pattern) (ha : d10869 p = 1) (hb : d112686 p = 1) : d141481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10863 q = 1) (hb : d112686 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10863, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10868 q = 1) (hb : d112686 q = 1) : d141480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10868, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10869 q = 1) (hb : d112686 q = 1) : d141481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10869, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25777 (p : Pattern) (ha : d10875 p = 1) (hb : d112686 p = 1) : d141487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d112686 q = 1) : d141485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d112686 q = 1) : d141486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d112686 q = 1) : d141487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25778 (p : Pattern) (ha : d10879 p = 1) (hb : d112686 p = 1) : d141491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d112686 q = 1) : d141489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d112686 q = 1) : d141490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10879 q = 1) (hb : d112686 q = 1) : d141491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25779 (p : Pattern) (ha : d10885 p = 1) (hb : d112686 p = 1) : d141497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d112686 q = 1) : d141492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25777 q ha hb
    | true =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25778 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d112686 q = 1) : d141493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d112686 q = 1) : d141494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d112686 q = 1) : d141495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d112686 q = 1) : d141496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d112686 q = 1) : d141497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25780 (p : Pattern) (ha : d10888 p = 1) (hb : d112686 p = 1) : d141500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d112686 q = 1) : d141485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d112686 q = 1) : d141486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d112686 q = 1) : d141500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25781 (p : Pattern) (ha : d10889 p = 1) (hb : d112686 p = 1) : d141501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d112686 q = 1) : d141489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d112686 q = 1) : d141490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10889 q = 1) (hb : d112686 q = 1) : d141501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10889, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25782 (p : Pattern) (ha : d10895 p = 1) (hb : d112686 p = 1) : d141507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d112686 q = 1) : d141492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25777 q ha hb
    | true =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25778 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d112686 q = 1) : d141493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d112686 q = 1) : d141494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d112686 q = 1) : d141495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d112686 q = 1) : d141496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d112686 q = 1) : d141502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25780 q ha hb
    | true =>
      simp only [d10890, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25781 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d112686 q = 1) : d141503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d112686 q = 1) : d141504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d112686 q = 1) : d141505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d112686 q = 1) : d141506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d112686 q = 1) : d141507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25783 (p : Pattern) (ha : d10992 p = 1) (hb : d112686 p = 1) : d141576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d112686 q = 1) : d141492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25777 q ha hb
    | true =>
      simp only [d10880, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25778 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d112686 q = 1) : d141493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d112686 q = 1) : d141494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d112686 q = 1) : d141495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d112686 q = 1) : d141496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d112686 q = 1) : d141571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25778 q ha hb
    | true =>
      simp only [d10987, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d112686 q = 1) : d141572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d112686 q = 1) : d141573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d112686 q = 1) : d141574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d112686 q = 1) : d141575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d112686 q = 1) : d141576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25784 (p : Pattern) (ha : d10998 p = 1) (hb : d112686 p = 1) : d141582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d112686 q = 1) : d141571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25778 q ha hb
    | true =>
      simp only [d10987, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d112686 q = 1) : d141572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d112686 q = 1) : d141573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d112686 q = 1) : d141574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d112686 q = 1) : d141575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d112686 q = 1) : d141577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25781 q ha hb
    | true =>
      simp only [d10993, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d112686 q = 1) : d141578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d112686 q = 1) : d141579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d112686 q = 1) : d141580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d112686 q = 1) : d141581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d112686 q = 1) : d141582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25785 (p : Pattern) (ha : d11007 p = 1) (hb : d112686 p = 1) : d141591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d112686 q = 1) : d141577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25781 q ha hb
    | true =>
      simp only [d10993, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d112686 q = 1) : d141578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d112686 q = 1) : d141579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d112686 q = 1) : d141580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d112686 q = 1) : d141581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d112686 q = 1) : d141591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25786 (p : Pattern) (ha : d11031 p = 1) (hb : d112686 p = 1) : d141611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11021 q = 1) (hb : d112686 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11021, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11030 q = 1) (hb : d112686 q = 1) : d141610 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11030, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11031 q = 1) (hb : d112686 q = 1) : d141611 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11031, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25787 (p : Pattern) (ha : d11076 p = 1) (hb : d112686 p = 1) : d141634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d112686 q = 1) : d141612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25786 q ha hb
    | true =>
      simp only [d11032, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d112686 q = 1) : d141613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11073 q = 1) (hb : d112686 q = 1) : d141631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11074 q = 1) (hb : d112686 q = 1) : d141632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11074, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11075 q = 1) (hb : d112686 q = 1) : d141633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11075, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11076 q = 1) (hb : d112686 q = 1) : d141634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11076, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25788 (p : Pattern) (ha : d11082 p = 1) (hb : d112686 p = 1) : d141640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d112686 q = 1) : d141635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25787 q ha hb
    | true =>
      simp only [d11077, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d112686 q = 1) : d141636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d112686 q = 1) : d141637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d112686 q = 1) : d141638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d112686 q = 1) : d141639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d112686 q = 1) : d141640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25789 (p : Pattern) (ha : d10900 p = 1) (hb : d112686 p = 1) : d141512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d112686 q = 1) : d141485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d112686 q = 1) : d141511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d112686 q = 1) : d141512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25790 (p : Pattern) (ha : d10902 p = 1) (hb : d112686 p = 1) : d141514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d112686 q = 1) : d141489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d112686 q = 1) : d141513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10902 q = 1) (hb : d112686 q = 1) : d141514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25791 (p : Pattern) (ha : d10909 p = 1) (hb : d112686 p = 1) : d141521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d112686 q = 1) : d141519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d112686 q = 1) : d141520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d112686 q = 1) : d141521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25792 (p : Pattern) (ha : d10912 p = 1) (hb : d112686 p = 1) : d141524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d112686 q = 1) : d141522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d112686 q = 1) : d141523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d112686 q = 1) : d141524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25793 (p : Pattern) (ha : d10921 p = 1) (hb : d112686 p = 1) : d141530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10916 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18332 q ha hb
    | true =>
      simp only [d10916, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10917 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10918 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10742 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10743 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10744 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10919 q = 1) (hb : d112686 q = 1) : d141528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10919, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10745 q = 1) (hb : d112686 q = 1) : d141389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10745, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10920 q = 1) (hb : d112686 q = 1) : d141529 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10920, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10921 q = 1) (hb : d112686 q = 1) : d141530 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10921, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25794 (p : Pattern) (ha : d10927 p = 1) (hb : d112686 p = 1) : d141536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d112686 q = 1) : d141531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25793 q ha hb
    | true =>
      simp only [d10922, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d112686 q = 1) : d141532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d112686 q = 1) : d141533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d112686 q = 1) : d141534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d112686 q = 1) : d141535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d112686 q = 1) : d141536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25795 (p : Pattern) (ha : d10955 p = 1) (hb : d112686 p = 1) : d141542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d112686 q = 1) : d141539 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d112686 q = 1) : d141540 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d112686 q = 1) : d141541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d112686 q = 1) : d141542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25796 (p : Pattern) (ha : d108861 p = 1) (hb : d112686 p = 1) : d141548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d112686 q = 1) : d141515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25789 q ha hb
    | true =>
      simp only [d10903, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25790 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d112686 q = 1) : d141516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d112686 q = 1) : d141517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d112686 q = 1) : d141518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d112686 q = 1) : d141525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25791 q ha hb
    | true =>
      simp only [d10913, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25792 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d112686 q = 1) : d141526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d112686 q = 1) : d141527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d112686 q = 1) : d141537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25794 q ha hb
    | true =>
      simp only [d10928, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25777 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d112686 q = 1) : d141538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d112686 q = 1) : d141543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25795 q ha hb
    | true =>
      simp only [d10956, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d112686 q = 1) : d141544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d112686 q = 1) : d141545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d112686 q = 1) : d141546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d112686 q = 1) : d141547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108861 q = 1) (hb : d112686 q = 1) : d141548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25797 (p : Pattern) (ha : d10962 p = 1) (hb : d112686 p = 1) : d141549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d112686 q = 1) : d141485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d112686 q = 1) : d141511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d112686 q = 1) : d141549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25798 (p : Pattern) (ha : d10963 p = 1) (hb : d112686 p = 1) : d141550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d112686 q = 1) : d141489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d112686 q = 1) : d141513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10963 q = 1) (hb : d112686 q = 1) : d141550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10963, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25799 (p : Pattern) (ha : d10968 p = 1) (hb : d112686 p = 1) : d141555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d112686 q = 1) : d141484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d112686 q = 1) : d141519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d112686 q = 1) : d141520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d112686 q = 1) : d141555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25800 (p : Pattern) (ha : d10969 p = 1) (hb : d112686 p = 1) : d141556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d112686 q = 1) : d141482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25776 q ha hb
    | true =>
      simp only [d10870, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d112686 q = 1) : d141483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d112686 q = 1) : d141488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d112686 q = 1) : d141522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d112686 q = 1) : d141523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10969 q = 1) (hb : d112686 q = 1) : d141556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10969, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25801 (p : Pattern) (ha : d10973 p = 1) (hb : d112686 p = 1) : d141560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d112686 q = 1) : d141531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25793 q ha hb
    | true =>
      simp only [d10922, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d112686 q = 1) : d141532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d112686 q = 1) : d141533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d112686 q = 1) : d141534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d112686 q = 1) : d141535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d112686 q = 1) : d141560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25802 (p : Pattern) (ha : d10979 p = 1) (hb : d112686 p = 1) : d141563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d112686 q = 1) : d141478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25775 q ha hb
    | true =>
      simp only [d10866, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d112686 q = 1) : d141479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d112686 q = 1) : d141539 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d112686 q = 1) : d141540 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d112686 q = 1) : d141541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d112686 q = 1) : d141563 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25803 (p : Pattern) (ha : d108866 p = 1) (hb : d112686 p = 1) : d141569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d112686 q = 1) : d141515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25789 q ha hb
    | true =>
      simp only [d10903, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25790 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d112686 q = 1) : d141516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d112686 q = 1) : d141517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d112686 q = 1) : d141518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d112686 q = 1) : d141525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25791 q ha hb
    | true =>
      simp only [d10913, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25792 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d112686 q = 1) : d141526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d112686 q = 1) : d141527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d112686 q = 1) : d141537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25794 q ha hb
    | true =>
      simp only [d10928, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25777 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d112686 q = 1) : d141538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d112686 q = 1) : d141543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25795 q ha hb
    | true =>
      simp only [d10956, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d112686 q = 1) : d141544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d112686 q = 1) : d141545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d112686 q = 1) : d141546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d112686 q = 1) : d141547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10964 q = 1) (hb : d112686 q = 1) : d141551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25797 q ha hb
    | true =>
      simp only [d10964, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25798 q ha hb
  have h16 (q : Pattern) (ha : d10965 q = 1) (hb : d112686 q = 1) : d141552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10966 q = 1) (hb : d112686 q = 1) : d141553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10966, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10967 q = 1) (hb : d112686 q = 1) : d141554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10970 q = 1) (hb : d112686 q = 1) : d141557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25799 q ha hb
    | true =>
      simp only [d10970, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25800 q ha hb
  have h20 (q : Pattern) (ha : d10971 q = 1) (hb : d112686 q = 1) : d141558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10972 q = 1) (hb : d112686 q = 1) : d141559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10972, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10974 q = 1) (hb : d112686 q = 1) : d141561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25801 q ha hb
    | true =>
      simp only [d10974, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25780 q ha hb
  have h23 (q : Pattern) (ha : d108862 q = 1) (hb : d112686 q = 1) : d141562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108862, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10980 q = 1) (hb : d112686 q = 1) : d141564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25802 q ha hb
    | true =>
      simp only [d10980, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10981 q = 1) (hb : d112686 q = 1) : d141565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10981, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108863 q = 1) (hb : d112686 q = 1) : d141566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108863, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108864 q = 1) (hb : d112686 q = 1) : d141567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108864, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108865 q = 1) (hb : d112686 q = 1) : d141568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108865, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108866 q = 1) (hb : d112686 q = 1) : d141569 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108866, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25804 (p : Pattern) (ha : d108873 p = 1) (hb : d112686 p = 1) : d141589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d112686 q = 1) : d141561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25801 q ha hb
    | true =>
      simp only [d10974, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25780 q ha hb
  have h2 (q : Pattern) (ha : d108862 q = 1) (hb : d112686 q = 1) : d141562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108862, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d112686 q = 1) : d141564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25802 q ha hb
    | true =>
      simp only [d10980, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d112686 q = 1) : d141565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d112686 q = 1) : d141566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d112686 q = 1) : d141587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d112686 q = 1) : d141588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d112686 q = 1) : d141589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25805 (p : Pattern) (ha : d11018 p = 1) (hb : d112686 p = 1) : d141599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11013 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18345 q ha hb
    | true =>
      simp only [d11013, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11014 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11015 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10814 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10815 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10816 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11016 q = 1) (hb : d112686 q = 1) : d141597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11016, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10817 q = 1) (hb : d112686 q = 1) : d141443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11017 q = 1) (hb : d112686 q = 1) : d141598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11017, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11018 q = 1) (hb : d112686 q = 1) : d141599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11018, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25806 (p : Pattern) (ha : d11023 p = 1) (hb : d112686 p = 1) : d141603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d112686 q = 1) : d141443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11021 q = 1) (hb : d112686 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11021, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11022 q = 1) (hb : d112686 q = 1) : d141602 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11022, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11023 q = 1) (hb : d112686 q = 1) : d141603 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11023, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25807 (p : Pattern) (ha : d11029 p = 1) (hb : d112686 p = 1) : d141609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d112686 q = 1) : d141600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25805 q ha hb
    | true =>
      simp only [d11019, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d112686 q = 1) : d141601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d112686 q = 1) : d141604 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25806 q ha hb
    | true =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d112686 q = 1) : d141605 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d112686 q = 1) : d141606 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d112686 q = 1) : d141607 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d112686 q = 1) : d141608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d112686 q = 1) : d141609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25808 (p : Pattern) (ha : d11037 p = 1) (hb : d112686 p = 1) : d141617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d112686 q = 1) : d141604 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25806 q ha hb
    | true =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d112686 q = 1) : d141605 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d112686 q = 1) : d141612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25786 q ha hb
    | true =>
      simp only [d11032, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d112686 q = 1) : d141613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11034 q = 1) (hb : d112686 q = 1) : d141614 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d112686 q = 1) : d141615 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11035, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d112686 q = 1) : d141616 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d112686 q = 1) : d141617 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25809 (p : Pattern) (ha : d11065 p = 1) (hb : d112686 p = 1) : d141623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d112686 q = 1) : d141604 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25806 q ha hb
    | true =>
      simp only [d11024, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d112686 q = 1) : d141605 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d112686 q = 1) : d141620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d112686 q = 1) : d141621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d112686 q = 1) : d141622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d112686 q = 1) : d141623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25810 (p : Pattern) (ha : d108883 p = 1) (hb : d112686 p = 1) : d141629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d112686 q = 1) : d141618 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25807 q ha hb
    | true =>
      simp only [d11038, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25808 q ha hb
  have h2 (q : Pattern) (ha : d108879 q = 1) (hb : d112686 q = 1) : d141619 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108879, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d112686 q = 1) : d141624 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25809 q ha hb
    | true =>
      simp only [d11066, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d112686 q = 1) : d141625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d112686 q = 1) : d141626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d112686 q = 1) : d141627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d112686 q = 1) : d141628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d112686 q = 1) : d141629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25811 (p : Pattern) (ha : d108889 p = 1) (hb : d112686 p = 1) : d141646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d112686 q = 1) : d141498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25779 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d112686 q = 1) : d141499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d112686 q = 1) : d141508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25779 q ha hb
    | true =>
      simp only [d10896, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25782 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d112686 q = 1) : d141509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d112686 q = 1) : d141510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108867 q = 1) (hb : d112686 q = 1) : d141570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25796 q ha hb
    | true =>
      simp only [d108867, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25803 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d112686 q = 1) : d141583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25783 q ha hb
    | true =>
      simp only [d10999, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25784 q ha hb
  have h8 (q : Pattern) (ha : d108868 q = 1) (hb : d112686 q = 1) : d141584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108869 q = 1) (hb : d112686 q = 1) : d141585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108869, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108870 q = 1) (hb : d112686 q = 1) : d141586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108870, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108874 q = 1) (hb : d112686 q = 1) : d141590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108874, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25804 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d112686 q = 1) : d141592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25785 q ha hb
  have h13 (q : Pattern) (ha : d108875 q = 1) (hb : d112686 q = 1) : d141593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108875, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108876 q = 1) (hb : d112686 q = 1) : d141594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108876, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108877 q = 1) (hb : d112686 q = 1) : d141595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108877, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108878 q = 1) (hb : d112686 q = 1) : d141596 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108878, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108884 q = 1) (hb : d112686 q = 1) : d141630 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108884, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25810 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d112686 q = 1) : d141641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25788 q ha hb
  have h19 (q : Pattern) (ha : d108885 q = 1) (hb : d112686 q = 1) : d141642 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108885, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108886 q = 1) (hb : d112686 q = 1) : d141643 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108886, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108887 q = 1) (hb : d112686 q = 1) : d141644 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108887, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108888 q = 1) (hb : d112686 q = 1) : d141645 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108888, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108889 q = 1) (hb : d112686 q = 1) : d141646 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108889, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25812 (p : Pattern) (ha : d108895 p = 1) (hb : d112686 p = 1) : d141652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d112686 q = 1) : d141647 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25811 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d112686 q = 1) : d141648 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d112686 q = 1) : d141649 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d112686 q = 1) : d141650 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d112686 q = 1) : d141651 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d112686 q = 1) : d141652 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25813 (p : Pattern) (ha : d11105 p = 1) (hb : d112686 p = 1) : d141656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d112686 q = 1) : d141654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11103 q = 1) (hb : d112686 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11103, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11104 q = 1) (hb : d112686 q = 1) : d141655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11104, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11105 q = 1) (hb : d112686 q = 1) : d141656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11105, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25814 (p : Pattern) (ha : d11109 p = 1) (hb : d112686 p = 1) : d141660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11099 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11100 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11101 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11103 q = 1) (hb : d112686 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11103, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11108 q = 1) (hb : d112686 q = 1) : d141659 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11108, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11109 q = 1) (hb : d112686 q = 1) : d141660 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11109, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25815 (p : Pattern) (ha : d11115 p = 1) (hb : d112686 p = 1) : d141666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d112686 q = 1) : d141664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d112686 q = 1) : d141665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d112686 q = 1) : d141666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25816 (p : Pattern) (ha : d11119 p = 1) (hb : d112686 p = 1) : d141670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d112686 q = 1) : d141668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d112686 q = 1) : d141669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11119 q = 1) (hb : d112686 q = 1) : d141670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25817 (p : Pattern) (ha : d11125 p = 1) (hb : d112686 p = 1) : d141676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d112686 q = 1) : d141671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25815 q ha hb
    | true =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25816 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d112686 q = 1) : d141672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d112686 q = 1) : d141673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d112686 q = 1) : d141674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d112686 q = 1) : d141675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d112686 q = 1) : d141676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25818 (p : Pattern) (ha : d11128 p = 1) (hb : d112686 p = 1) : d141679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d112686 q = 1) : d141664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d112686 q = 1) : d141665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d112686 q = 1) : d141679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25819 (p : Pattern) (ha : d11129 p = 1) (hb : d112686 p = 1) : d141680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d112686 q = 1) : d141668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d112686 q = 1) : d141669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11129 q = 1) (hb : d112686 q = 1) : d141680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11129, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25820 (p : Pattern) (ha : d11135 p = 1) (hb : d112686 p = 1) : d141686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d112686 q = 1) : d141671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25815 q ha hb
    | true =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25816 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d112686 q = 1) : d141672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d112686 q = 1) : d141673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d112686 q = 1) : d141674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d112686 q = 1) : d141675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d112686 q = 1) : d141681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25818 q ha hb
    | true =>
      simp only [d11130, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25819 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d112686 q = 1) : d141682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d112686 q = 1) : d141683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d112686 q = 1) : d141684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d112686 q = 1) : d141685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d112686 q = 1) : d141686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25821 (p : Pattern) (ha : d11243 p = 1) (hb : d112686 p = 1) : d141758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d112686 q = 1) : d141671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25815 q ha hb
    | true =>
      simp only [d11120, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25816 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d112686 q = 1) : d141672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d112686 q = 1) : d141673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d112686 q = 1) : d141674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d112686 q = 1) : d141675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d112686 q = 1) : d141753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25816 q ha hb
    | true =>
      simp only [d11238, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d112686 q = 1) : d141754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d112686 q = 1) : d141755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d112686 q = 1) : d141756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d112686 q = 1) : d141757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d112686 q = 1) : d141758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25822 (p : Pattern) (ha : d11249 p = 1) (hb : d112686 p = 1) : d141764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d112686 q = 1) : d141753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25816 q ha hb
    | true =>
      simp only [d11238, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d112686 q = 1) : d141754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d112686 q = 1) : d141755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d112686 q = 1) : d141756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d112686 q = 1) : d141757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d112686 q = 1) : d141759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25819 q ha hb
    | true =>
      simp only [d11244, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d112686 q = 1) : d141760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d112686 q = 1) : d141761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d112686 q = 1) : d141762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d112686 q = 1) : d141763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d112686 q = 1) : d141764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25823 (p : Pattern) (ha : d11258 p = 1) (hb : d112686 p = 1) : d141773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d112686 q = 1) : d141759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25819 q ha hb
    | true =>
      simp only [d11244, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d112686 q = 1) : d141760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d112686 q = 1) : d141761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d112686 q = 1) : d141762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d112686 q = 1) : d141763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d112686 q = 1) : d141773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25824 (p : Pattern) (ha : d11289 p = 1) (hb : d112686 p = 1) : d141797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11271 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11272 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11273 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11279 q = 1) (hb : d112686 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11279, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11288 q = 1) (hb : d112686 q = 1) : d141796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11288, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11289 q = 1) (hb : d112686 q = 1) : d141797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11289, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25825 (p : Pattern) (ha : d11345 p = 1) (hb : d112686 p = 1) : d141820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d112686 q = 1) : d141798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25824 q ha hb
    | true =>
      simp only [d11290, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d112686 q = 1) : d141799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11342 q = 1) (hb : d112686 q = 1) : d141817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11343 q = 1) (hb : d112686 q = 1) : d141818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11343, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11344 q = 1) (hb : d112686 q = 1) : d141819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11344, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11345 q = 1) (hb : d112686 q = 1) : d141820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11345, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25826 (p : Pattern) (ha : d11351 p = 1) (hb : d112686 p = 1) : d141826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d112686 q = 1) : d141821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25825 q ha hb
    | true =>
      simp only [d11346, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d112686 q = 1) : d141822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d112686 q = 1) : d141823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d112686 q = 1) : d141824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d112686 q = 1) : d141825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d112686 q = 1) : d141826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25827 (p : Pattern) (ha : d11140 p = 1) (hb : d112686 p = 1) : d141691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d112686 q = 1) : d141664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d112686 q = 1) : d141690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d112686 q = 1) : d141691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25828 (p : Pattern) (ha : d11142 p = 1) (hb : d112686 p = 1) : d141693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d112686 q = 1) : d141668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d112686 q = 1) : d141692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11142 q = 1) (hb : d112686 q = 1) : d141693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25829 (p : Pattern) (ha : d11149 p = 1) (hb : d112686 p = 1) : d141700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d112686 q = 1) : d141698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d112686 q = 1) : d141699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d112686 q = 1) : d141700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25830 (p : Pattern) (ha : d11152 p = 1) (hb : d112686 p = 1) : d141703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d112686 q = 1) : d141701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d112686 q = 1) : d141702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d112686 q = 1) : d141703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25831 (p : Pattern) (ha : d11161 p = 1) (hb : d112686 p = 1) : d141712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11156 q = 1) (hb : d112686 q = 1) : d141707 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d112686, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18371 q ha hb
    | true =>
      simp only [d11156, d112686, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11157 q = 1) (hb : d112686 q = 1) : d141708 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11158 q = 1) (hb : d112686 q = 1) : d141709 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11096 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11097 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11098 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11159 q = 1) (hb : d112686 q = 1) : d141710 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11159, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11099 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11100 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11101 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11102 q = 1) (hb : d112686 q = 1) : d141654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11160 q = 1) (hb : d112686 q = 1) : d141711 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11160, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11161 q = 1) (hb : d112686 q = 1) : d141712 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11161, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25832 (p : Pattern) (ha : d11167 p = 1) (hb : d112686 p = 1) : d141718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d112686 q = 1) : d141713 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25831 q ha hb
    | true =>
      simp only [d11162, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d112686 q = 1) : d141714 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d112686 q = 1) : d141715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d112686 q = 1) : d141716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d112686 q = 1) : d141717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d112686 q = 1) : d141718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25833 (p : Pattern) (ha : d5456 p = 1) (hb : d94753 p = 1) : d4913 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d755 q = 1) : d755 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5455 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5456 q = 1) (hb : d94753 q = 1) : d4913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5456, d94753, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5456, d94753, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25834 (p : Pattern) (ha : d11200 p = 1) (hb : d112686 p = 1) : d141656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d112686 q = 1) : d141654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11195 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25833 q ha hb
    | true =>
      simp only [d11195, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11196 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11196, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11197 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11197, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11198 q = 1) (hb : d112686 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11198, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11199 q = 1) (hb : d112686 q = 1) : d141655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11199, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11200 q = 1) (hb : d112686 q = 1) : d141656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11200, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25835 (p : Pattern) (ha : d11206 p = 1) (hb : d112686 p = 1) : d141724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25834 q ha hb
    | true =>
      simp only [d11201, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d112686 q = 1) : d141721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d112686 q = 1) : d141722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d112686 q = 1) : d141723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d112686 q = 1) : d141724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25836 (p : Pattern) (ha : d108901 p = 1) (hb : d112686 p = 1) : d141730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d112686 q = 1) : d141694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25827 q ha hb
    | true =>
      simp only [d11143, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25828 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d112686 q = 1) : d141695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d112686 q = 1) : d141696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d112686 q = 1) : d141697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d112686 q = 1) : d141704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25829 q ha hb
    | true =>
      simp only [d11153, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25830 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d112686 q = 1) : d141705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d112686 q = 1) : d141706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d112686 q = 1) : d141719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25832 q ha hb
    | true =>
      simp only [d11168, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25815 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d112686 q = 1) : d141720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d112686 q = 1) : d141725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25835 q ha hb
    | true =>
      simp only [d11207, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d112686 q = 1) : d141726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d112686 q = 1) : d141727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d112686 q = 1) : d141728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d112686 q = 1) : d141729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108901 q = 1) (hb : d112686 q = 1) : d141730 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25837 (p : Pattern) (ha : d11213 p = 1) (hb : d112686 p = 1) : d141731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d112686 q = 1) : d141664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d112686 q = 1) : d141690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d112686 q = 1) : d141731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25838 (p : Pattern) (ha : d11214 p = 1) (hb : d112686 p = 1) : d141732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d112686 q = 1) : d141668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d112686 q = 1) : d141692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11214 q = 1) (hb : d112686 q = 1) : d141732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11214, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25839 (p : Pattern) (ha : d11219 p = 1) (hb : d112686 p = 1) : d141737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d112686 q = 1) : d141663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d112686 q = 1) : d141698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d112686 q = 1) : d141699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d112686 q = 1) : d141737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25840 (p : Pattern) (ha : d11220 p = 1) (hb : d112686 p = 1) : d141738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d112686 q = 1) : d141661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25814 q ha hb
    | true =>
      simp only [d11110, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d112686 q = 1) : d141662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d112686 q = 1) : d141667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d112686 q = 1) : d141701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d112686 q = 1) : d141702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11220 q = 1) (hb : d112686 q = 1) : d141738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11220, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25841 (p : Pattern) (ha : d11224 p = 1) (hb : d112686 p = 1) : d141742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d112686 q = 1) : d141713 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25831 q ha hb
    | true =>
      simp only [d11162, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d112686 q = 1) : d141714 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25813 q ha hb
    | true =>
      simp only [d11106, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d112686 q = 1) : d141715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d112686 q = 1) : d141716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d112686 q = 1) : d141717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d112686 q = 1) : d141742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25842 (p : Pattern) (ha : d11230 p = 1) (hb : d112686 p = 1) : d141745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d112686 q = 1) : d141657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25834 q ha hb
    | true =>
      simp only [d11201, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d112686 q = 1) : d141658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d112686 q = 1) : d141721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d112686 q = 1) : d141722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d112686 q = 1) : d141723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d112686 q = 1) : d141745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25843 (p : Pattern) (ha : d108906 p = 1) (hb : d112686 p = 1) : d141751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d112686 q = 1) : d141694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25827 q ha hb
    | true =>
      simp only [d11143, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25828 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d112686 q = 1) : d141695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d112686 q = 1) : d141696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d112686 q = 1) : d141697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d112686 q = 1) : d141704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25829 q ha hb
    | true =>
      simp only [d11153, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25830 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d112686 q = 1) : d141705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d112686 q = 1) : d141706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d112686 q = 1) : d141719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25832 q ha hb
    | true =>
      simp only [d11168, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25815 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d112686 q = 1) : d141720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d112686 q = 1) : d141725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25835 q ha hb
    | true =>
      simp only [d11207, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d112686 q = 1) : d141726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d112686 q = 1) : d141727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d112686 q = 1) : d141728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d112686 q = 1) : d141729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11215 q = 1) (hb : d112686 q = 1) : d141733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25837 q ha hb
    | true =>
      simp only [d11215, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25838 q ha hb
  have h16 (q : Pattern) (ha : d11216 q = 1) (hb : d112686 q = 1) : d141734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11217 q = 1) (hb : d112686 q = 1) : d141735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11217, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11218 q = 1) (hb : d112686 q = 1) : d141736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11221 q = 1) (hb : d112686 q = 1) : d141739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25839 q ha hb
    | true =>
      simp only [d11221, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25840 q ha hb
  have h20 (q : Pattern) (ha : d11222 q = 1) (hb : d112686 q = 1) : d141740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11223 q = 1) (hb : d112686 q = 1) : d141741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11223, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11225 q = 1) (hb : d112686 q = 1) : d141743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25841 q ha hb
    | true =>
      simp only [d11225, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25818 q ha hb
  have h23 (q : Pattern) (ha : d108902 q = 1) (hb : d112686 q = 1) : d141744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108902, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11231 q = 1) (hb : d112686 q = 1) : d141746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25842 q ha hb
    | true =>
      simp only [d11231, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11232 q = 1) (hb : d112686 q = 1) : d141747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11232, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108903 q = 1) (hb : d112686 q = 1) : d141748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108903, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108904 q = 1) (hb : d112686 q = 1) : d141749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108904, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108905 q = 1) (hb : d112686 q = 1) : d141750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108905, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108906 q = 1) (hb : d112686 q = 1) : d141751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108906, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25844 (p : Pattern) (ha : d108913 p = 1) (hb : d112686 p = 1) : d141771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d112686 q = 1) : d141743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25841 q ha hb
    | true =>
      simp only [d11225, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25818 q ha hb
  have h2 (q : Pattern) (ha : d108902 q = 1) (hb : d112686 q = 1) : d141744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108902, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d112686 q = 1) : d141746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25842 q ha hb
    | true =>
      simp only [d11231, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d112686 q = 1) : d141747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d112686 q = 1) : d141748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d112686 q = 1) : d141769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d112686 q = 1) : d141770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d112686 q = 1) : d141771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25845 (p : Pattern) (ha : d11276 p = 1) (hb : d112686 p = 1) : d141785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11264 q = 1) (hb : d112686 q = 1) : d141779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d112686, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18384 q ha hb
    | true =>
      simp only [d11264, d112686, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11265 q = 1) (hb : d112686 q = 1) : d141780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11266 q = 1) (hb : d112686 q = 1) : d141781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11267 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11268 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11269 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11270 q = 1) (hb : d112686 q = 1) : d141782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11270, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11271 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11272 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11273 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11274 q = 1) (hb : d112686 q = 1) : d141783 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11275 q = 1) (hb : d112686 q = 1) : d141784 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11275, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11276 q = 1) (hb : d112686 q = 1) : d141785 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11276, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25846 (p : Pattern) (ha : d11281 p = 1) (hb : d112686 p = 1) : d141789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d112686 q = 1) : d141783 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11279 q = 1) (hb : d112686 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11279, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11280 q = 1) (hb : d112686 q = 1) : d141788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11280, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11281 q = 1) (hb : d112686 q = 1) : d141789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11281, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25847 (p : Pattern) (ha : d11287 p = 1) (hb : d112686 p = 1) : d141795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d112686 q = 1) : d141786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25845 q ha hb
    | true =>
      simp only [d11277, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d112686 q = 1) : d141787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d112686 q = 1) : d141790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25846 q ha hb
    | true =>
      simp only [d11282, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d112686 q = 1) : d141791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d112686 q = 1) : d141792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d112686 q = 1) : d141793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d112686 q = 1) : d141794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d112686 q = 1) : d141795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25848 (p : Pattern) (ha : d11295 p = 1) (hb : d112686 p = 1) : d141803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d112686 q = 1) : d141790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25846 q ha hb
    | true =>
      simp only [d11282, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d112686 q = 1) : d141791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d112686 q = 1) : d141798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25824 q ha hb
    | true =>
      simp only [d11290, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d112686 q = 1) : d141799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11292 q = 1) (hb : d112686 q = 1) : d141800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11293 q = 1) (hb : d112686 q = 1) : d141801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11293, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11294 q = 1) (hb : d112686 q = 1) : d141802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11294, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11295 q = 1) (hb : d112686 q = 1) : d141803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11295, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25849 (p : Pattern) (ha : d5500 p = 1) (hb : d94753 p = 1) : d6210 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d975 q = 1) : d975 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5500 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5500, d94753, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5500, d94753, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25850 (p : Pattern) (ha : d11328 p = 1) (hb : d112686 p = 1) : d141789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d112686 q = 1) : d141783 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11323 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25849 q ha hb
    | true =>
      simp only [d11323, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11324 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11324, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11325 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11325, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11326 q = 1) (hb : d112686 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11326, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11327 q = 1) (hb : d112686 q = 1) : d141788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11327, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11328 q = 1) (hb : d112686 q = 1) : d141789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11328, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25851 (p : Pattern) (ha : d11334 p = 1) (hb : d112686 p = 1) : d141809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d112686 q = 1) : d141790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25850 q ha hb
    | true =>
      simp only [d11329, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d112686 q = 1) : d141791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d112686 q = 1) : d141806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d112686 q = 1) : d141807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d112686 q = 1) : d141808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d112686 q = 1) : d141809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25852 (p : Pattern) (ha : d108923 p = 1) (hb : d112686 p = 1) : d141815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d112686 q = 1) : d141804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25847 q ha hb
    | true =>
      simp only [d11296, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25848 q ha hb
  have h2 (q : Pattern) (ha : d108919 q = 1) (hb : d112686 q = 1) : d141805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108919, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d112686 q = 1) : d141810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25851 q ha hb
    | true =>
      simp only [d11335, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d112686 q = 1) : d141811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d112686 q = 1) : d141812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d112686 q = 1) : d141813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d112686 q = 1) : d141814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d112686 q = 1) : d141815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25853 (p : Pattern) (ha : d108929 p = 1) (hb : d112686 p = 1) : d141832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d112686 q = 1) : d141677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25817 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d112686 q = 1) : d141678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d112686 q = 1) : d141687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25817 q ha hb
    | true =>
      simp only [d11136, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25820 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d112686 q = 1) : d141688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d112686 q = 1) : d141689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108907 q = 1) (hb : d112686 q = 1) : d141752 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25836 q ha hb
    | true =>
      simp only [d108907, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25843 q ha hb
  have h7 (q : Pattern) (ha : d11250 q = 1) (hb : d112686 q = 1) : d141765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25821 q ha hb
    | true =>
      simp only [d11250, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25822 q ha hb
  have h8 (q : Pattern) (ha : d108908 q = 1) (hb : d112686 q = 1) : d141766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108909 q = 1) (hb : d112686 q = 1) : d141767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108909, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108910 q = 1) (hb : d112686 q = 1) : d141768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108910, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108914 q = 1) (hb : d112686 q = 1) : d141772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108914, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25844 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d112686 q = 1) : d141774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25823 q ha hb
  have h13 (q : Pattern) (ha : d108915 q = 1) (hb : d112686 q = 1) : d141775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108915, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108916 q = 1) (hb : d112686 q = 1) : d141776 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108916, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108917 q = 1) (hb : d112686 q = 1) : d141777 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108917, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108918 q = 1) (hb : d112686 q = 1) : d141778 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108918, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108924 q = 1) (hb : d112686 q = 1) : d141816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108924, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25852 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d112686 q = 1) : d141827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25826 q ha hb
  have h19 (q : Pattern) (ha : d108925 q = 1) (hb : d112686 q = 1) : d141828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108925, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108926 q = 1) (hb : d112686 q = 1) : d141829 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108926, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108927 q = 1) (hb : d112686 q = 1) : d141830 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108927, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108928 q = 1) (hb : d112686 q = 1) : d141831 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108928, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108929 q = 1) (hb : d112686 q = 1) : d141832 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108929, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25854 (p : Pattern) (ha : d108935 p = 1) (hb : d112686 p = 1) : d141838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d112686 q = 1) : d141833 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25853 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d112686 q = 1) : d141834 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d112686 q = 1) : d141835 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d112686 q = 1) : d141836 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d112686 q = 1) : d141837 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d112686 q = 1) : d141838 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25855 (p : Pattern) (ha : d11375 p = 1) (hb : d112686 p = 1) : d141843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d112686 q = 1) : d141841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11373 q = 1) (hb : d112686 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11373, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11374 q = 1) (hb : d112686 q = 1) : d141842 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11374, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11375 q = 1) (hb : d112686 q = 1) : d141843 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11375, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25856 (p : Pattern) (ha : d11379 p = 1) (hb : d112686 p = 1) : d141847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11369 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11370 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11371 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11373 q = 1) (hb : d112686 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11373, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11378 q = 1) (hb : d112686 q = 1) : d141846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11378, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11379 q = 1) (hb : d112686 q = 1) : d141847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11379, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25857 (p : Pattern) (ha : d11385 p = 1) (hb : d112686 p = 1) : d141853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d112686 q = 1) : d141851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d112686 q = 1) : d141852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11385 q = 1) (hb : d112686 q = 1) : d141853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25858 (p : Pattern) (ha : d11389 p = 1) (hb : d112686 p = 1) : d141857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d112686 q = 1) : d141855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d112686 q = 1) : d141856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11389 q = 1) (hb : d112686 q = 1) : d141857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11389, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25859 (p : Pattern) (ha : d11395 p = 1) (hb : d112686 p = 1) : d141863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d112686 q = 1) : d141858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25857 q ha hb
    | true =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25858 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d112686 q = 1) : d141859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d112686 q = 1) : d141860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d112686 q = 1) : d141861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d112686 q = 1) : d141862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11395 q = 1) (hb : d112686 q = 1) : d141863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25860 (p : Pattern) (ha : d11398 p = 1) (hb : d112686 p = 1) : d141866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d112686 q = 1) : d141851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d112686 q = 1) : d141852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11398 q = 1) (hb : d112686 q = 1) : d141866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11398, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25861 (p : Pattern) (ha : d11399 p = 1) (hb : d112686 p = 1) : d141867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d112686 q = 1) : d141855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d112686 q = 1) : d141856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11399 q = 1) (hb : d112686 q = 1) : d141867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11399, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25862 (p : Pattern) (ha : d11405 p = 1) (hb : d112686 p = 1) : d141873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d112686 q = 1) : d141858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25857 q ha hb
    | true =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25858 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d112686 q = 1) : d141859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d112686 q = 1) : d141860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d112686 q = 1) : d141861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d112686 q = 1) : d141862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11400 q = 1) (hb : d112686 q = 1) : d141868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25860 q ha hb
    | true =>
      simp only [d11400, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25861 q ha hb
  have h7 (q : Pattern) (ha : d11401 q = 1) (hb : d112686 q = 1) : d141869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11402 q = 1) (hb : d112686 q = 1) : d141870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11403 q = 1) (hb : d112686 q = 1) : d141871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11404 q = 1) (hb : d112686 q = 1) : d141872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11405 q = 1) (hb : d112686 q = 1) : d141873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11405, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25863 (p : Pattern) (ha : d11513 p = 1) (hb : d112686 p = 1) : d141945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d112686 q = 1) : d141858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25857 q ha hb
    | true =>
      simp only [d11390, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25858 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d112686 q = 1) : d141859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d112686 q = 1) : d141860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d112686 q = 1) : d141861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d112686 q = 1) : d141862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d112686 q = 1) : d141940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25858 q ha hb
    | true =>
      simp only [d11508, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d112686 q = 1) : d141941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d112686 q = 1) : d141942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d112686 q = 1) : d141943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d112686 q = 1) : d141944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11513 q = 1) (hb : d112686 q = 1) : d141945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11513, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25864 (p : Pattern) (ha : d11519 p = 1) (hb : d112686 p = 1) : d141951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11508 q = 1) (hb : d112686 q = 1) : d141940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25858 q ha hb
    | true =>
      simp only [d11508, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11509 q = 1) (hb : d112686 q = 1) : d141941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11510 q = 1) (hb : d112686 q = 1) : d141942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11510, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11511 q = 1) (hb : d112686 q = 1) : d141943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11512 q = 1) (hb : d112686 q = 1) : d141944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11514 q = 1) (hb : d112686 q = 1) : d141946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25861 q ha hb
    | true =>
      simp only [d11514, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11515 q = 1) (hb : d112686 q = 1) : d141947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11516 q = 1) (hb : d112686 q = 1) : d141948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11516, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11517 q = 1) (hb : d112686 q = 1) : d141949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11518 q = 1) (hb : d112686 q = 1) : d141950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11519 q = 1) (hb : d112686 q = 1) : d141951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11519, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25865 (p : Pattern) (ha : d11528 p = 1) (hb : d112686 p = 1) : d141960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11514 q = 1) (hb : d112686 q = 1) : d141946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25861 q ha hb
    | true =>
      simp only [d11514, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11515 q = 1) (hb : d112686 q = 1) : d141947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11516 q = 1) (hb : d112686 q = 1) : d141948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11516, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11517 q = 1) (hb : d112686 q = 1) : d141949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11518 q = 1) (hb : d112686 q = 1) : d141950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11528 q = 1) (hb : d112686 q = 1) : d141960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11528, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25866 (p : Pattern) (ha : d11559 p = 1) (hb : d112686 p = 1) : d141984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11541 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11542 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11543 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11549 q = 1) (hb : d112686 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11549, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11558 q = 1) (hb : d112686 q = 1) : d141983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11558, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11559 q = 1) (hb : d112686 q = 1) : d141984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11559, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25867 (p : Pattern) (ha : d11615 p = 1) (hb : d112686 p = 1) : d142007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11560 q = 1) (hb : d112686 q = 1) : d141985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25866 q ha hb
    | true =>
      simp only [d11560, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11561 q = 1) (hb : d112686 q = 1) : d141986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11612 q = 1) (hb : d112686 q = 1) : d142004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11612, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11613 q = 1) (hb : d112686 q = 1) : d142005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11613, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11614 q = 1) (hb : d112686 q = 1) : d142006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11614, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11615 q = 1) (hb : d112686 q = 1) : d142007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11615, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25868 (p : Pattern) (ha : d11621 p = 1) (hb : d112686 p = 1) : d142013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11616 q = 1) (hb : d112686 q = 1) : d142008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25867 q ha hb
    | true =>
      simp only [d11616, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11617 q = 1) (hb : d112686 q = 1) : d142009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11617, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11618 q = 1) (hb : d112686 q = 1) : d142010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11618, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11619 q = 1) (hb : d112686 q = 1) : d142011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11619, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11620 q = 1) (hb : d112686 q = 1) : d142012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11620, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11621 q = 1) (hb : d112686 q = 1) : d142013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11621, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25869 (p : Pattern) (ha : d11410 p = 1) (hb : d112686 p = 1) : d141878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d112686 q = 1) : d141851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d112686 q = 1) : d141877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11410 q = 1) (hb : d112686 q = 1) : d141878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25870 (p : Pattern) (ha : d11412 p = 1) (hb : d112686 p = 1) : d141880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d112686 q = 1) : d141855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d112686 q = 1) : d141879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11412 q = 1) (hb : d112686 q = 1) : d141880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11412, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25871 (p : Pattern) (ha : d11419 p = 1) (hb : d112686 p = 1) : d141887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d112686 q = 1) : d141885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d112686 q = 1) : d141886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11419 q = 1) (hb : d112686 q = 1) : d141887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25872 (p : Pattern) (ha : d11422 p = 1) (hb : d112686 p = 1) : d141890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d112686 q = 1) : d141888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d112686 q = 1) : d141889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d112686 q = 1) : d141890 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11422, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25873 (p : Pattern) (ha : d11431 p = 1) (hb : d112686 p = 1) : d141899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11426 q = 1) (hb : d112686 q = 1) : d141894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d112686, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18411 q ha hb
    | true =>
      simp only [d11426, d112686, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11427 q = 1) (hb : d112686 q = 1) : d141895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11428 q = 1) (hb : d112686 q = 1) : d141896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11366 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11367 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11368 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11429 q = 1) (hb : d112686 q = 1) : d141897 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11429, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11369 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11370 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11371 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11372 q = 1) (hb : d112686 q = 1) : d141841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11430 q = 1) (hb : d112686 q = 1) : d141898 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11430, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11431 q = 1) (hb : d112686 q = 1) : d141899 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11431, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25874 (p : Pattern) (ha : d11437 p = 1) (hb : d112686 p = 1) : d141905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d112686 q = 1) : d141900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25873 q ha hb
    | true =>
      simp only [d11432, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d112686 q = 1) : d141901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d112686 q = 1) : d141902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d112686 q = 1) : d141903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d112686 q = 1) : d141904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d112686 q = 1) : d141905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25875 (p : Pattern) (ha : d5545 p = 1) (hb : d94753 p = 1) : d5009 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1125 q = 1) : d1125 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5545 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5545, d94753, d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5545, d94753, d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25876 (p : Pattern) (ha : d11470 p = 1) (hb : d112686 p = 1) : d141843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d112686 q = 1) : d141841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11465 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25875 q ha hb
    | true =>
      simp only [d11465, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11466 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11466, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11467 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11467, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11468 q = 1) (hb : d112686 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11468, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11469 q = 1) (hb : d112686 q = 1) : d141842 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11469, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11470 q = 1) (hb : d112686 q = 1) : d141843 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11470, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25877 (p : Pattern) (ha : d11476 p = 1) (hb : d112686 p = 1) : d141911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25876 q ha hb
    | true =>
      simp only [d11471, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d112686 q = 1) : d141908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d112686 q = 1) : d141909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d112686 q = 1) : d141910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d112686 q = 1) : d141911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25878 (p : Pattern) (ha : d108942 p = 1) (hb : d112686 p = 1) : d141917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d112686 q = 1) : d141881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25869 q ha hb
    | true =>
      simp only [d11413, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25870 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d112686 q = 1) : d141882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d112686 q = 1) : d141883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d112686 q = 1) : d141884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d112686 q = 1) : d141891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25871 q ha hb
    | true =>
      simp only [d11423, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25872 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d112686 q = 1) : d141892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d112686 q = 1) : d141893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d112686 q = 1) : d141906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25874 q ha hb
    | true =>
      simp only [d11438, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25857 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d112686 q = 1) : d141907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d112686 q = 1) : d141912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25877 q ha hb
    | true =>
      simp only [d11477, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d112686 q = 1) : d141913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d112686 q = 1) : d141914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d112686 q = 1) : d141915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d112686 q = 1) : d141916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108942 q = 1) (hb : d112686 q = 1) : d141917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25879 (p : Pattern) (ha : d11483 p = 1) (hb : d112686 p = 1) : d141918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d112686 q = 1) : d141851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d112686 q = 1) : d141877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11483 q = 1) (hb : d112686 q = 1) : d141918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11483, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25880 (p : Pattern) (ha : d11484 p = 1) (hb : d112686 p = 1) : d141919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d112686 q = 1) : d141855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d112686 q = 1) : d141879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11484 q = 1) (hb : d112686 q = 1) : d141919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11484, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25881 (p : Pattern) (ha : d11489 p = 1) (hb : d112686 p = 1) : d141924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d112686 q = 1) : d141850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d112686 q = 1) : d141885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d112686 q = 1) : d141886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11489 q = 1) (hb : d112686 q = 1) : d141924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11489, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25882 (p : Pattern) (ha : d11490 p = 1) (hb : d112686 p = 1) : d141925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d112686 q = 1) : d141848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25856 q ha hb
    | true =>
      simp only [d11380, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d112686 q = 1) : d141849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d112686 q = 1) : d141854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d112686 q = 1) : d141888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d112686 q = 1) : d141889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11490 q = 1) (hb : d112686 q = 1) : d141925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11490, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25883 (p : Pattern) (ha : d11494 p = 1) (hb : d112686 p = 1) : d141929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d112686 q = 1) : d141900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25873 q ha hb
    | true =>
      simp only [d11432, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d112686 q = 1) : d141901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25855 q ha hb
    | true =>
      simp only [d11376, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d112686 q = 1) : d141902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d112686 q = 1) : d141903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d112686 q = 1) : d141904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d112686 q = 1) : d141929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25884 (p : Pattern) (ha : d11500 p = 1) (hb : d112686 p = 1) : d141932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d112686 q = 1) : d141844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25876 q ha hb
    | true =>
      simp only [d11471, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d112686 q = 1) : d141845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d112686 q = 1) : d141908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d112686 q = 1) : d141909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d112686 q = 1) : d141910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d112686 q = 1) : d141932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25885 (p : Pattern) (ha : d108947 p = 1) (hb : d112686 p = 1) : d141938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d112686 q = 1) : d141881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25869 q ha hb
    | true =>
      simp only [d11413, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25870 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d112686 q = 1) : d141882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d112686 q = 1) : d141883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d112686 q = 1) : d141884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d112686 q = 1) : d141891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25871 q ha hb
    | true =>
      simp only [d11423, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25872 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d112686 q = 1) : d141892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d112686 q = 1) : d141893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d112686 q = 1) : d141906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25874 q ha hb
    | true =>
      simp only [d11438, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25857 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d112686 q = 1) : d141907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d112686 q = 1) : d141912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25877 q ha hb
    | true =>
      simp only [d11477, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d112686 q = 1) : d141913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d112686 q = 1) : d141914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d112686 q = 1) : d141915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d112686 q = 1) : d141916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11485 q = 1) (hb : d112686 q = 1) : d141920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25879 q ha hb
    | true =>
      simp only [d11485, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25880 q ha hb
  have h16 (q : Pattern) (ha : d11486 q = 1) (hb : d112686 q = 1) : d141921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11487 q = 1) (hb : d112686 q = 1) : d141922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11487, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11488 q = 1) (hb : d112686 q = 1) : d141923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11491 q = 1) (hb : d112686 q = 1) : d141926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25881 q ha hb
    | true =>
      simp only [d11491, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25882 q ha hb
  have h20 (q : Pattern) (ha : d11492 q = 1) (hb : d112686 q = 1) : d141927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11493 q = 1) (hb : d112686 q = 1) : d141928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11493, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11495 q = 1) (hb : d112686 q = 1) : d141930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25883 q ha hb
    | true =>
      simp only [d11495, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25860 q ha hb
  have h23 (q : Pattern) (ha : d108943 q = 1) (hb : d112686 q = 1) : d141931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108943, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11501 q = 1) (hb : d112686 q = 1) : d141933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25884 q ha hb
    | true =>
      simp only [d11501, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11502 q = 1) (hb : d112686 q = 1) : d141934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11502, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108944 q = 1) (hb : d112686 q = 1) : d141935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108944, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108945 q = 1) (hb : d112686 q = 1) : d141936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108945, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108946 q = 1) (hb : d112686 q = 1) : d141937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108946, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108947 q = 1) (hb : d112686 q = 1) : d141938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108947, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25886 (p : Pattern) (ha : d108954 p = 1) (hb : d112686 p = 1) : d141958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d112686 q = 1) : d141930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25883 q ha hb
    | true =>
      simp only [d11495, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25860 q ha hb
  have h2 (q : Pattern) (ha : d108943 q = 1) (hb : d112686 q = 1) : d141931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108943, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d112686 q = 1) : d141933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25884 q ha hb
    | true =>
      simp only [d11501, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d112686 q = 1) : d141934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d112686 q = 1) : d141935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d112686 q = 1) : d141956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d112686 q = 1) : d141957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d112686 q = 1) : d141958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25887 (p : Pattern) (ha : d11546 p = 1) (hb : d112686 p = 1) : d141972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11534 q = 1) (hb : d112686 q = 1) : d141966 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d112686, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18424 q ha hb
    | true =>
      simp only [d11534, d112686, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11535 q = 1) (hb : d112686 q = 1) : d141967 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11536 q = 1) (hb : d112686 q = 1) : d141968 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11537 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11538 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11539 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11540 q = 1) (hb : d112686 q = 1) : d141969 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11540, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11541 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11542 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11543 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11544 q = 1) (hb : d112686 q = 1) : d141970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11545 q = 1) (hb : d112686 q = 1) : d141971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11545, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11546 q = 1) (hb : d112686 q = 1) : d141972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11546, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25888 (p : Pattern) (ha : d11551 p = 1) (hb : d112686 p = 1) : d141976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d112686 q = 1) : d141970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11549 q = 1) (hb : d112686 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11549, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11550 q = 1) (hb : d112686 q = 1) : d141975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11550, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11551 q = 1) (hb : d112686 q = 1) : d141976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11551, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25889 (p : Pattern) (ha : d11557 p = 1) (hb : d112686 p = 1) : d141982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d112686 q = 1) : d141973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25887 q ha hb
    | true =>
      simp only [d11547, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d112686 q = 1) : d141974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d112686 q = 1) : d141977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25888 q ha hb
    | true =>
      simp only [d11552, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d112686 q = 1) : d141978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d112686 q = 1) : d141979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d112686 q = 1) : d141980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d112686 q = 1) : d141981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d112686 q = 1) : d141982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25890 (p : Pattern) (ha : d11565 p = 1) (hb : d112686 p = 1) : d141990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d112686 q = 1) : d141977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25888 q ha hb
    | true =>
      simp only [d11552, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d112686 q = 1) : d141978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d112686 q = 1) : d141985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25866 q ha hb
    | true =>
      simp only [d11560, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d112686 q = 1) : d141986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11562 q = 1) (hb : d112686 q = 1) : d141987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11563 q = 1) (hb : d112686 q = 1) : d141988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11563, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11564 q = 1) (hb : d112686 q = 1) : d141989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11564, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11565 q = 1) (hb : d112686 q = 1) : d141990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11565, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25891 (p : Pattern) (ha : d5589 p = 1) (hb : d94753 p = 1) : d6349 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1395 q = 1) : d1395 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5588 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5589 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5589, d94753, d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5589, d94753, d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25892 (p : Pattern) (ha : d11598 p = 1) (hb : d112686 p = 1) : d141976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d112686 q = 1) : d141970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11593 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25891 q ha hb
    | true =>
      simp only [d11593, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11594 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11594, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11595 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11595, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11596 q = 1) (hb : d112686 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11596, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11597 q = 1) (hb : d112686 q = 1) : d141975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11597, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11598 q = 1) (hb : d112686 q = 1) : d141976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11598, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25893 (p : Pattern) (ha : d11604 p = 1) (hb : d112686 p = 1) : d141996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d112686 q = 1) : d141977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25892 q ha hb
    | true =>
      simp only [d11599, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d112686 q = 1) : d141978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d112686 q = 1) : d141993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d112686 q = 1) : d141994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d112686 q = 1) : d141995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d112686 q = 1) : d141996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25894 (p : Pattern) (ha : d108964 p = 1) (hb : d112686 p = 1) : d142002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d112686 q = 1) : d141991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25889 q ha hb
    | true =>
      simp only [d11566, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25890 q ha hb
  have h2 (q : Pattern) (ha : d108960 q = 1) (hb : d112686 q = 1) : d141992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108960, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d112686 q = 1) : d141997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25893 q ha hb
    | true =>
      simp only [d11605, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d112686 q = 1) : d141998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d112686 q = 1) : d141999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d112686 q = 1) : d142000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d112686 q = 1) : d142001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d112686 q = 1) : d142002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25895 (p : Pattern) (ha : d108970 p = 1) (hb : d112686 p = 1) : d142019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d112686 q = 1) : d141864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25859 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d112686 q = 1) : d141865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d112686 q = 1) : d141874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25859 q ha hb
    | true =>
      simp only [d11406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25862 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d112686 q = 1) : d141875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d112686 q = 1) : d141876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108948 q = 1) (hb : d112686 q = 1) : d141939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25878 q ha hb
    | true =>
      simp only [d108948, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25885 q ha hb
  have h7 (q : Pattern) (ha : d11520 q = 1) (hb : d112686 q = 1) : d141952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25863 q ha hb
    | true =>
      simp only [d11520, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25864 q ha hb
  have h8 (q : Pattern) (ha : d108949 q = 1) (hb : d112686 q = 1) : d141953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108950 q = 1) (hb : d112686 q = 1) : d141954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108950, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108951 q = 1) (hb : d112686 q = 1) : d141955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108951, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108955 q = 1) (hb : d112686 q = 1) : d141959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108955, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25886 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d112686 q = 1) : d141961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25865 q ha hb
  have h13 (q : Pattern) (ha : d108956 q = 1) (hb : d112686 q = 1) : d141962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108956, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108957 q = 1) (hb : d112686 q = 1) : d141963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108957, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108958 q = 1) (hb : d112686 q = 1) : d141964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108958, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108959 q = 1) (hb : d112686 q = 1) : d141965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108959, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108965 q = 1) (hb : d112686 q = 1) : d142003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108965, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25894 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d112686 q = 1) : d142014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25868 q ha hb
  have h19 (q : Pattern) (ha : d108966 q = 1) (hb : d112686 q = 1) : d142015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108966, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108967 q = 1) (hb : d112686 q = 1) : d142016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108967, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108968 q = 1) (hb : d112686 q = 1) : d142017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108968, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108969 q = 1) (hb : d112686 q = 1) : d142018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108969, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108970 q = 1) (hb : d112686 q = 1) : d142019 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108970, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25896 (p : Pattern) (ha : d108976 p = 1) (hb : d112686 p = 1) : d142025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d112686 q = 1) : d142020 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25895 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d112686 q = 1) : d142021 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d112686 q = 1) : d142022 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d112686 q = 1) : d142023 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d112686 q = 1) : d142024 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d112686 q = 1) : d142025 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25897 (p : Pattern) (ha : d11646 p = 1) (hb : d112686 p = 1) : d142031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d112686 q = 1) : d142029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11644 q = 1) (hb : d112686 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11644, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11645 q = 1) (hb : d112686 q = 1) : d142030 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11645, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11646 q = 1) (hb : d112686 q = 1) : d142031 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11646, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25898 (p : Pattern) (ha : d11650 p = 1) (hb : d112686 p = 1) : d142035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11640 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11641 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11642 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11644 q = 1) (hb : d112686 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11644, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11649 q = 1) (hb : d112686 q = 1) : d142034 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11649, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11650 q = 1) (hb : d112686 q = 1) : d142035 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11650, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25899 (p : Pattern) (ha : d11656 p = 1) (hb : d112686 p = 1) : d142041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d112686 q = 1) : d142039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d112686 q = 1) : d142040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11656 q = 1) (hb : d112686 q = 1) : d142041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25900 (p : Pattern) (ha : d11660 p = 1) (hb : d112686 p = 1) : d142045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d112686 q = 1) : d142043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d112686 q = 1) : d142044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11660 q = 1) (hb : d112686 q = 1) : d142045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11660, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25901 (p : Pattern) (ha : d11666 p = 1) (hb : d112686 p = 1) : d142051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d112686 q = 1) : d142046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25899 q ha hb
    | true =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25900 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d112686 q = 1) : d142047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d112686 q = 1) : d142048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d112686 q = 1) : d142049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d112686 q = 1) : d142050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11666 q = 1) (hb : d112686 q = 1) : d142051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25902 (p : Pattern) (ha : d11669 p = 1) (hb : d112686 p = 1) : d142054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d112686 q = 1) : d142039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d112686 q = 1) : d142040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11669 q = 1) (hb : d112686 q = 1) : d142054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11669, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25903 (p : Pattern) (ha : d11670 p = 1) (hb : d112686 p = 1) : d142055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d112686 q = 1) : d142043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d112686 q = 1) : d142044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11670 q = 1) (hb : d112686 q = 1) : d142055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11670, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25904 (p : Pattern) (ha : d11676 p = 1) (hb : d112686 p = 1) : d142061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d112686 q = 1) : d142046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25899 q ha hb
    | true =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25900 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d112686 q = 1) : d142047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d112686 q = 1) : d142048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d112686 q = 1) : d142049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d112686 q = 1) : d142050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11671 q = 1) (hb : d112686 q = 1) : d142056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25902 q ha hb
    | true =>
      simp only [d11671, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25903 q ha hb
  have h7 (q : Pattern) (ha : d11672 q = 1) (hb : d112686 q = 1) : d142057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11673 q = 1) (hb : d112686 q = 1) : d142058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11673, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11674 q = 1) (hb : d112686 q = 1) : d142059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11675 q = 1) (hb : d112686 q = 1) : d142060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11676 q = 1) (hb : d112686 q = 1) : d142061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11676, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25905 (p : Pattern) (ha : d11784 p = 1) (hb : d112686 p = 1) : d142133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d112686 q = 1) : d142046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25899 q ha hb
    | true =>
      simp only [d11661, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25900 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d112686 q = 1) : d142047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d112686 q = 1) : d142048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d112686 q = 1) : d142049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d112686 q = 1) : d142050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d112686 q = 1) : d142128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25900 q ha hb
    | true =>
      simp only [d11779, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d112686 q = 1) : d142129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d112686 q = 1) : d142130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d112686 q = 1) : d142131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d112686 q = 1) : d142132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11784 q = 1) (hb : d112686 q = 1) : d142133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11784, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25906 (p : Pattern) (ha : d11790 p = 1) (hb : d112686 p = 1) : d142139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11779 q = 1) (hb : d112686 q = 1) : d142128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25900 q ha hb
    | true =>
      simp only [d11779, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11780 q = 1) (hb : d112686 q = 1) : d142129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11781 q = 1) (hb : d112686 q = 1) : d142130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11781, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11782 q = 1) (hb : d112686 q = 1) : d142131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11783 q = 1) (hb : d112686 q = 1) : d142132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11785 q = 1) (hb : d112686 q = 1) : d142134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25903 q ha hb
    | true =>
      simp only [d11785, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11786 q = 1) (hb : d112686 q = 1) : d142135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11787 q = 1) (hb : d112686 q = 1) : d142136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11787, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11788 q = 1) (hb : d112686 q = 1) : d142137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11789 q = 1) (hb : d112686 q = 1) : d142138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11790 q = 1) (hb : d112686 q = 1) : d142139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11790, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25907 (p : Pattern) (ha : d11799 p = 1) (hb : d112686 p = 1) : d142148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11785 q = 1) (hb : d112686 q = 1) : d142134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25903 q ha hb
    | true =>
      simp only [d11785, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11786 q = 1) (hb : d112686 q = 1) : d142135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11787 q = 1) (hb : d112686 q = 1) : d142136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11787, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11788 q = 1) (hb : d112686 q = 1) : d142137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11789 q = 1) (hb : d112686 q = 1) : d142138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11799 q = 1) (hb : d112686 q = 1) : d142148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11799, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25908 (p : Pattern) (ha : d11830 p = 1) (hb : d112686 p = 1) : d142172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11812 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11813 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11814 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11820 q = 1) (hb : d112686 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11820, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11829 q = 1) (hb : d112686 q = 1) : d142171 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11829, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11830 q = 1) (hb : d112686 q = 1) : d142172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11830, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25909 (p : Pattern) (ha : d11886 p = 1) (hb : d112686 p = 1) : d142195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11831 q = 1) (hb : d112686 q = 1) : d142173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25908 q ha hb
    | true =>
      simp only [d11831, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11832 q = 1) (hb : d112686 q = 1) : d142174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11883 q = 1) (hb : d112686 q = 1) : d142192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11883, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11884 q = 1) (hb : d112686 q = 1) : d142193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11884, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11885 q = 1) (hb : d112686 q = 1) : d142194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11885, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11886 q = 1) (hb : d112686 q = 1) : d142195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11886, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25910 (p : Pattern) (ha : d11892 p = 1) (hb : d112686 p = 1) : d142201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11887 q = 1) (hb : d112686 q = 1) : d142196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25909 q ha hb
    | true =>
      simp only [d11887, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11888 q = 1) (hb : d112686 q = 1) : d142197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11888, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11889 q = 1) (hb : d112686 q = 1) : d142198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11889, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11890 q = 1) (hb : d112686 q = 1) : d142199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11890, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11891 q = 1) (hb : d112686 q = 1) : d142200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11891, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11892 q = 1) (hb : d112686 q = 1) : d142201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11892, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25911 (p : Pattern) (ha : d11681 p = 1) (hb : d112686 p = 1) : d142066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d112686 q = 1) : d142039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d112686 q = 1) : d142065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11681 q = 1) (hb : d112686 q = 1) : d142066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25912 (p : Pattern) (ha : d11683 p = 1) (hb : d112686 p = 1) : d142068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d112686 q = 1) : d142043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d112686 q = 1) : d142067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11683 q = 1) (hb : d112686 q = 1) : d142068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11683, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25913 (p : Pattern) (ha : d11690 p = 1) (hb : d112686 p = 1) : d142075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d112686 q = 1) : d142073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d112686 q = 1) : d142074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11690 q = 1) (hb : d112686 q = 1) : d142075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25914 (p : Pattern) (ha : d11693 p = 1) (hb : d112686 p = 1) : d142078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d112686 q = 1) : d142076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d112686 q = 1) : d142077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d112686 q = 1) : d142078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11693, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25915 (p : Pattern) (ha : d11702 p = 1) (hb : d112686 p = 1) : d142087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11697 q = 1) (hb : d112686 q = 1) : d142082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d112686, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18451 q ha hb
    | true =>
      simp only [d11697, d112686, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11698 q = 1) (hb : d112686 q = 1) : d142083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11699 q = 1) (hb : d112686 q = 1) : d142084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11637 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11638 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11639 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11700 q = 1) (hb : d112686 q = 1) : d142085 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11700, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11640 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11641 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11642 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11643 q = 1) (hb : d112686 q = 1) : d142029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11701 q = 1) (hb : d112686 q = 1) : d142086 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11701, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11702 q = 1) (hb : d112686 q = 1) : d142087 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11702, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25916 (p : Pattern) (ha : d11708 p = 1) (hb : d112686 p = 1) : d142093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d112686 q = 1) : d142088 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25915 q ha hb
    | true =>
      simp only [d11703, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d112686 q = 1) : d142089 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d112686 q = 1) : d142090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d112686 q = 1) : d142091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d112686 q = 1) : d142092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d112686 q = 1) : d142093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25917 (p : Pattern) (ha : d5635 p = 1) (hb : d94753 p = 1) : d5120 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1586 q = 1) : d1586 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5634 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5635 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5635, d94753, d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5635, d94753, d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25918 (p : Pattern) (ha : d11741 p = 1) (hb : d112686 p = 1) : d142031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d112686 q = 1) : d142029 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11736 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25917 q ha hb
    | true =>
      simp only [d11736, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11737 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11737, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11738 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11738, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11739 q = 1) (hb : d112686 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11739, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11740 q = 1) (hb : d112686 q = 1) : d142030 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11740, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11741 q = 1) (hb : d112686 q = 1) : d142031 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11741, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25919 (p : Pattern) (ha : d11747 p = 1) (hb : d112686 p = 1) : d142099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25918 q ha hb
    | true =>
      simp only [d11742, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d112686 q = 1) : d142096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d112686 q = 1) : d142097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d112686 q = 1) : d142098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d112686 q = 1) : d142099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25920 (p : Pattern) (ha : d108984 p = 1) (hb : d112686 p = 1) : d142105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d112686 q = 1) : d142069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25911 q ha hb
    | true =>
      simp only [d11684, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25912 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d112686 q = 1) : d142070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d112686 q = 1) : d142071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d112686 q = 1) : d142072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d112686 q = 1) : d142079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25913 q ha hb
    | true =>
      simp only [d11694, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25914 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d112686 q = 1) : d142080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d112686 q = 1) : d142081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d112686 q = 1) : d142094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25916 q ha hb
    | true =>
      simp only [d11709, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25899 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d112686 q = 1) : d142095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d112686 q = 1) : d142100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25919 q ha hb
    | true =>
      simp only [d11748, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d112686 q = 1) : d142101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d112686 q = 1) : d142102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d112686 q = 1) : d142103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d112686 q = 1) : d142104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108984 q = 1) (hb : d112686 q = 1) : d142105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25921 (p : Pattern) (ha : d11754 p = 1) (hb : d112686 p = 1) : d142106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d112686 q = 1) : d142039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d112686 q = 1) : d142065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11754 q = 1) (hb : d112686 q = 1) : d142106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11754, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25922 (p : Pattern) (ha : d11755 p = 1) (hb : d112686 p = 1) : d142107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d112686 q = 1) : d142043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d112686 q = 1) : d142067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11755 q = 1) (hb : d112686 q = 1) : d142107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11755, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25923 (p : Pattern) (ha : d11760 p = 1) (hb : d112686 p = 1) : d142112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d112686 q = 1) : d142038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d112686 q = 1) : d142073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d112686 q = 1) : d142074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11760 q = 1) (hb : d112686 q = 1) : d142112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11760, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25924 (p : Pattern) (ha : d11761 p = 1) (hb : d112686 p = 1) : d142113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d112686 q = 1) : d142036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25898 q ha hb
    | true =>
      simp only [d11651, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d112686 q = 1) : d142037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d112686 q = 1) : d142042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d112686 q = 1) : d142076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d112686 q = 1) : d142077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11761 q = 1) (hb : d112686 q = 1) : d142113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11761, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25925 (p : Pattern) (ha : d11765 p = 1) (hb : d112686 p = 1) : d142117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d112686 q = 1) : d142088 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25915 q ha hb
    | true =>
      simp only [d11703, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d112686 q = 1) : d142089 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25897 q ha hb
    | true =>
      simp only [d11647, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d112686 q = 1) : d142090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d112686 q = 1) : d142091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d112686 q = 1) : d142092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d112686 q = 1) : d142117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25926 (p : Pattern) (ha : d11771 p = 1) (hb : d112686 p = 1) : d142120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d112686 q = 1) : d142032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25918 q ha hb
    | true =>
      simp only [d11742, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d112686 q = 1) : d142033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d112686 q = 1) : d142096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d112686 q = 1) : d142097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d112686 q = 1) : d142098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d112686 q = 1) : d142120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25927 (p : Pattern) (ha : d108989 p = 1) (hb : d112686 p = 1) : d142126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d112686 q = 1) : d142069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25911 q ha hb
    | true =>
      simp only [d11684, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25912 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d112686 q = 1) : d142070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d112686 q = 1) : d142071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d112686 q = 1) : d142072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d112686 q = 1) : d142079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25913 q ha hb
    | true =>
      simp only [d11694, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25914 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d112686 q = 1) : d142080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d112686 q = 1) : d142081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d112686 q = 1) : d142094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25916 q ha hb
    | true =>
      simp only [d11709, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25899 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d112686 q = 1) : d142095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d112686 q = 1) : d142100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25919 q ha hb
    | true =>
      simp only [d11748, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d112686 q = 1) : d142101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d112686 q = 1) : d142102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d112686 q = 1) : d142103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d112686 q = 1) : d142104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11756 q = 1) (hb : d112686 q = 1) : d142108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25921 q ha hb
    | true =>
      simp only [d11756, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25922 q ha hb
  have h16 (q : Pattern) (ha : d11757 q = 1) (hb : d112686 q = 1) : d142109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11758 q = 1) (hb : d112686 q = 1) : d142110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11758, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11759 q = 1) (hb : d112686 q = 1) : d142111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11762 q = 1) (hb : d112686 q = 1) : d142114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25923 q ha hb
    | true =>
      simp only [d11762, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25924 q ha hb
  have h20 (q : Pattern) (ha : d11763 q = 1) (hb : d112686 q = 1) : d142115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11764 q = 1) (hb : d112686 q = 1) : d142116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11764, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11766 q = 1) (hb : d112686 q = 1) : d142118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25925 q ha hb
    | true =>
      simp only [d11766, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25902 q ha hb
  have h23 (q : Pattern) (ha : d108985 q = 1) (hb : d112686 q = 1) : d142119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108985, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11772 q = 1) (hb : d112686 q = 1) : d142121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25926 q ha hb
    | true =>
      simp only [d11772, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11773 q = 1) (hb : d112686 q = 1) : d142122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11773, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108986 q = 1) (hb : d112686 q = 1) : d142123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108986, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108987 q = 1) (hb : d112686 q = 1) : d142124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108987, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108988 q = 1) (hb : d112686 q = 1) : d142125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108988, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108989 q = 1) (hb : d112686 q = 1) : d142126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108989, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25928 (p : Pattern) (ha : d108996 p = 1) (hb : d112686 p = 1) : d142146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d112686 q = 1) : d142118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25925 q ha hb
    | true =>
      simp only [d11766, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25902 q ha hb
  have h2 (q : Pattern) (ha : d108985 q = 1) (hb : d112686 q = 1) : d142119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108985, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11772 q = 1) (hb : d112686 q = 1) : d142121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25926 q ha hb
    | true =>
      simp only [d11772, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11773 q = 1) (hb : d112686 q = 1) : d142122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11773, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d112686 q = 1) : d142123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108986, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d112686 q = 1) : d142144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d112686 q = 1) : d142145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d112686 q = 1) : d142146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25929 (p : Pattern) (ha : d11817 p = 1) (hb : d112686 p = 1) : d142160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11805 q = 1) (hb : d112686 q = 1) : d142154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d112686, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18464 q ha hb
    | true =>
      simp only [d11805, d112686, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11806 q = 1) (hb : d112686 q = 1) : d142155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11806, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11807 q = 1) (hb : d112686 q = 1) : d142156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11807, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11808 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11809 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11810 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11811 q = 1) (hb : d112686 q = 1) : d142157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11811, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11812 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11813 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11814 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11815 q = 1) (hb : d112686 q = 1) : d142158 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11816 q = 1) (hb : d112686 q = 1) : d142159 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11816, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11817 q = 1) (hb : d112686 q = 1) : d142160 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11817, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25930 (p : Pattern) (ha : d11822 p = 1) (hb : d112686 p = 1) : d142164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11812 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11813 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11814 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11815 q = 1) (hb : d112686 q = 1) : d142158 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11820 q = 1) (hb : d112686 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11820, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11821 q = 1) (hb : d112686 q = 1) : d142163 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11821, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11822 q = 1) (hb : d112686 q = 1) : d142164 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11822, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25931 (p : Pattern) (ha : d11828 p = 1) (hb : d112686 p = 1) : d142170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d112686 q = 1) : d142161 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25929 q ha hb
    | true =>
      simp only [d11818, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d112686 q = 1) : d142162 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11823 q = 1) (hb : d112686 q = 1) : d142165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25930 q ha hb
    | true =>
      simp only [d11823, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11824 q = 1) (hb : d112686 q = 1) : d142166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11825 q = 1) (hb : d112686 q = 1) : d142167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d112686 q = 1) : d142168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11826, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d112686 q = 1) : d142169 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d112686 q = 1) : d142170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25932 (p : Pattern) (ha : d11836 p = 1) (hb : d112686 p = 1) : d142178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d112686 q = 1) : d142165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25930 q ha hb
    | true =>
      simp only [d11823, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d112686 q = 1) : d142166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11831 q = 1) (hb : d112686 q = 1) : d142173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25908 q ha hb
    | true =>
      simp only [d11831, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11832 q = 1) (hb : d112686 q = 1) : d142174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11833 q = 1) (hb : d112686 q = 1) : d142175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11834 q = 1) (hb : d112686 q = 1) : d142176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11834, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11835 q = 1) (hb : d112686 q = 1) : d142177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11835, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11836 q = 1) (hb : d112686 q = 1) : d142178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11836, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25933 (p : Pattern) (ha : d5679 p = 1) (hb : d94753 p = 1) : d6495 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1872 q = 1) : d1872 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5679 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5679, d94753, d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5679, d94753, d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25934 (p : Pattern) (ha : d11869 p = 1) (hb : d112686 p = 1) : d142164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11812 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11813 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11814 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11815 q = 1) (hb : d112686 q = 1) : d142158 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11864 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11864, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25933 q ha hb
    | true =>
      simp only [d11864, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11865 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11865, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11865, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11866 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11866, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11866, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11867 q = 1) (hb : d112686 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11867, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11867, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11868 q = 1) (hb : d112686 q = 1) : d142163 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11868, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11869 q = 1) (hb : d112686 q = 1) : d142164 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11869, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25935 (p : Pattern) (ha : d11875 p = 1) (hb : d112686 p = 1) : d142184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d112686 q = 1) : d142165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25934 q ha hb
    | true =>
      simp only [d11870, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d112686 q = 1) : d142166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11872 q = 1) (hb : d112686 q = 1) : d142181 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11873 q = 1) (hb : d112686 q = 1) : d142182 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11873, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11874 q = 1) (hb : d112686 q = 1) : d142183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11874, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11875 q = 1) (hb : d112686 q = 1) : d142184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11875, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25936 (p : Pattern) (ha : d109006 p = 1) (hb : d112686 p = 1) : d142190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d112686 q = 1) : d142179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25931 q ha hb
    | true =>
      simp only [d11837, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25932 q ha hb
  have h2 (q : Pattern) (ha : d109002 q = 1) (hb : d112686 q = 1) : d142180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109002, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11876 q = 1) (hb : d112686 q = 1) : d142185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25935 q ha hb
    | true =>
      simp only [d11876, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11877 q = 1) (hb : d112686 q = 1) : d142186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11877, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d112686 q = 1) : d142187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109003, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d112686 q = 1) : d142188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d112686 q = 1) : d142189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d112686 q = 1) : d142190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25937 (p : Pattern) (ha : d109012 p = 1) (hb : d112686 p = 1) : d142207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d112686 q = 1) : d142052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25901 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d112686 q = 1) : d142053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d112686 q = 1) : d142062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25901 q ha hb
    | true =>
      simp only [d11677, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25904 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d112686 q = 1) : d142063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d112686 q = 1) : d142064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108990 q = 1) (hb : d112686 q = 1) : d142127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25920 q ha hb
    | true =>
      simp only [d108990, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25927 q ha hb
  have h7 (q : Pattern) (ha : d11791 q = 1) (hb : d112686 q = 1) : d142140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25905 q ha hb
    | true =>
      simp only [d11791, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25906 q ha hb
  have h8 (q : Pattern) (ha : d108991 q = 1) (hb : d112686 q = 1) : d142141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108991, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108992 q = 1) (hb : d112686 q = 1) : d142142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108992, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108993 q = 1) (hb : d112686 q = 1) : d142143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108993, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108997 q = 1) (hb : d112686 q = 1) : d142147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108997, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25928 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d112686 q = 1) : d142149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25907 q ha hb
  have h13 (q : Pattern) (ha : d108998 q = 1) (hb : d112686 q = 1) : d142150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108998, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108999 q = 1) (hb : d112686 q = 1) : d142151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108999, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109000 q = 1) (hb : d112686 q = 1) : d142152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109000, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109001 q = 1) (hb : d112686 q = 1) : d142153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109001, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109007 q = 1) (hb : d112686 q = 1) : d142191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109007, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25936 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d112686 q = 1) : d142202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25910 q ha hb
  have h19 (q : Pattern) (ha : d109008 q = 1) (hb : d112686 q = 1) : d142203 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109008, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d109009 q = 1) (hb : d112686 q = 1) : d142204 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109009, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d109010 q = 1) (hb : d112686 q = 1) : d142205 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109010, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109011 q = 1) (hb : d112686 q = 1) : d142206 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109011, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109012 q = 1) (hb : d112686 q = 1) : d142207 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109012, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25938 (p : Pattern) (ha : d109018 p = 1) (hb : d112686 p = 1) : d142213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d112686 q = 1) : d142208 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25937 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d112686 q = 1) : d142209 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d112686 q = 1) : d142210 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d112686 q = 1) : d142211 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d112686 q = 1) : d142212 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d112686 q = 1) : d142213 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25939 (p : Pattern) (ha : d11918 p = 1) (hb : d112686 p = 1) : d142220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11912 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11913 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11914 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11915 q = 1) (hb : d112686 q = 1) : d142218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11916 q = 1) (hb : d112686 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11916, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11917 q = 1) (hb : d112686 q = 1) : d142219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11917, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11918 q = 1) (hb : d112686 q = 1) : d142220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11918, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25940 (p : Pattern) (ha : d11922 p = 1) (hb : d112686 p = 1) : d142224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11912 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11913 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11914 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11916 q = 1) (hb : d112686 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11916, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11921 q = 1) (hb : d112686 q = 1) : d142223 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11921, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11921, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11922 q = 1) (hb : d112686 q = 1) : d142224 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11922, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11922, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25941 (p : Pattern) (ha : d11928 p = 1) (hb : d112686 p = 1) : d142230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d112686 q = 1) : d142228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d112686 q = 1) : d142229 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11928 q = 1) (hb : d112686 q = 1) : d142230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25942 (p : Pattern) (ha : d11932 p = 1) (hb : d112686 p = 1) : d142234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d112686 q = 1) : d142232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d112686 q = 1) : d142233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11932 q = 1) (hb : d112686 q = 1) : d142234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11932, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11932, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25943 (p : Pattern) (ha : d11938 p = 1) (hb : d112686 p = 1) : d142240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d112686 q = 1) : d142235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25941 q ha hb
    | true =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25942 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d112686 q = 1) : d142236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d112686 q = 1) : d142237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d112686 q = 1) : d142238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d112686 q = 1) : d142239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11938 q = 1) (hb : d112686 q = 1) : d142240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25944 (p : Pattern) (ha : d11941 p = 1) (hb : d112686 p = 1) : d142243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d112686 q = 1) : d142228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d112686 q = 1) : d142229 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11941 q = 1) (hb : d112686 q = 1) : d142243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11941, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25945 (p : Pattern) (ha : d11942 p = 1) (hb : d112686 p = 1) : d142244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d112686 q = 1) : d142232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d112686 q = 1) : d142233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11942 q = 1) (hb : d112686 q = 1) : d142244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11942, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11942, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25946 (p : Pattern) (ha : d11948 p = 1) (hb : d112686 p = 1) : d142250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d112686 q = 1) : d142235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25941 q ha hb
    | true =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25942 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d112686 q = 1) : d142236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d112686 q = 1) : d142237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d112686 q = 1) : d142238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d112686 q = 1) : d142239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11943 q = 1) (hb : d112686 q = 1) : d142245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25944 q ha hb
    | true =>
      simp only [d11943, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25945 q ha hb
  have h7 (q : Pattern) (ha : d11944 q = 1) (hb : d112686 q = 1) : d142246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11945 q = 1) (hb : d112686 q = 1) : d142247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11945, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11946 q = 1) (hb : d112686 q = 1) : d142248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11947 q = 1) (hb : d112686 q = 1) : d142249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11948 q = 1) (hb : d112686 q = 1) : d142250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11948, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25947 (p : Pattern) (ha : d12056 p = 1) (hb : d112686 p = 1) : d142322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d112686 q = 1) : d142235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25941 q ha hb
    | true =>
      simp only [d11933, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25942 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d112686 q = 1) : d142236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d112686 q = 1) : d142237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d112686 q = 1) : d142238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d112686 q = 1) : d142239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d112686 q = 1) : d142317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25942 q ha hb
    | true =>
      simp only [d12051, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d112686 q = 1) : d142318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d112686 q = 1) : d142319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d112686 q = 1) : d142320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d112686 q = 1) : d142321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12056 q = 1) (hb : d112686 q = 1) : d142322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12056, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25948 (p : Pattern) (ha : d12062 p = 1) (hb : d112686 p = 1) : d142328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12051 q = 1) (hb : d112686 q = 1) : d142317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25942 q ha hb
    | true =>
      simp only [d12051, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12052 q = 1) (hb : d112686 q = 1) : d142318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12053 q = 1) (hb : d112686 q = 1) : d142319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12053, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12054 q = 1) (hb : d112686 q = 1) : d142320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12055 q = 1) (hb : d112686 q = 1) : d142321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12057 q = 1) (hb : d112686 q = 1) : d142323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25945 q ha hb
    | true =>
      simp only [d12057, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12058 q = 1) (hb : d112686 q = 1) : d142324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12059 q = 1) (hb : d112686 q = 1) : d142325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12059, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12060 q = 1) (hb : d112686 q = 1) : d142326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12061 q = 1) (hb : d112686 q = 1) : d142327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12062 q = 1) (hb : d112686 q = 1) : d142328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12062, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12062, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25949 (p : Pattern) (ha : d12071 p = 1) (hb : d112686 p = 1) : d142337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12057 q = 1) (hb : d112686 q = 1) : d142323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25945 q ha hb
    | true =>
      simp only [d12057, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12058 q = 1) (hb : d112686 q = 1) : d142324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12059 q = 1) (hb : d112686 q = 1) : d142325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12059, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12060 q = 1) (hb : d112686 q = 1) : d142326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12061 q = 1) (hb : d112686 q = 1) : d142327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12071 q = 1) (hb : d112686 q = 1) : d142337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12071, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12071, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25950 (p : Pattern) (ha : d12102 p = 1) (hb : d112686 p = 1) : d142361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12084 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12085 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12086 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12092 q = 1) (hb : d112686 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12092, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12101 q = 1) (hb : d112686 q = 1) : d142360 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12101, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12101, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12102 q = 1) (hb : d112686 q = 1) : d142361 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12102, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12102, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25951 (p : Pattern) (ha : d12158 p = 1) (hb : d112686 p = 1) : d142384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12103 q = 1) (hb : d112686 q = 1) : d142362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25950 q ha hb
    | true =>
      simp only [d12103, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12104 q = 1) (hb : d112686 q = 1) : d142363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12155 q = 1) (hb : d112686 q = 1) : d142381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12155, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12155, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12156 q = 1) (hb : d112686 q = 1) : d142382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12156, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12156, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12157 q = 1) (hb : d112686 q = 1) : d142383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12157, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12157, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12158 q = 1) (hb : d112686 q = 1) : d142384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12158, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12158, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25952 (p : Pattern) (ha : d12164 p = 1) (hb : d112686 p = 1) : d142390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12159 q = 1) (hb : d112686 q = 1) : d142385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12159, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25951 q ha hb
    | true =>
      simp only [d12159, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12160 q = 1) (hb : d112686 q = 1) : d142386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12160, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12160, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12161 q = 1) (hb : d112686 q = 1) : d142387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12161, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12161, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12162 q = 1) (hb : d112686 q = 1) : d142388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12162, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12162, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12163 q = 1) (hb : d112686 q = 1) : d142389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12163, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12163, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12164 q = 1) (hb : d112686 q = 1) : d142390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12164, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12164, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25953 (p : Pattern) (ha : d11953 p = 1) (hb : d112686 p = 1) : d142255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d112686 q = 1) : d142228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d112686 q = 1) : d142254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11953 q = 1) (hb : d112686 q = 1) : d142255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25954 (p : Pattern) (ha : d11955 p = 1) (hb : d112686 p = 1) : d142257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d112686 q = 1) : d142232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d112686 q = 1) : d142256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11955 q = 1) (hb : d112686 q = 1) : d142257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11955, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11955, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25955 (p : Pattern) (ha : d11962 p = 1) (hb : d112686 p = 1) : d142264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d112686 q = 1) : d142262 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d112686 q = 1) : d142263 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11962 q = 1) (hb : d112686 q = 1) : d142264 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25956 (p : Pattern) (ha : d11965 p = 1) (hb : d112686 p = 1) : d142267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d112686 q = 1) : d142265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d112686 q = 1) : d142266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d112686 q = 1) : d142267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11965, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11965, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25957 (p : Pattern) (ha : d11974 p = 1) (hb : d112686 p = 1) : d142276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11969 q = 1) (hb : d112686 q = 1) : d142271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d112686, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18491 q ha hb
    | true =>
      simp only [d11969, d112686, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11970 q = 1) (hb : d112686 q = 1) : d142272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11970, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11971 q = 1) (hb : d112686 q = 1) : d142273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11971, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11909 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11910 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11911 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11972 q = 1) (hb : d112686 q = 1) : d142274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11972, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11912 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11913 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11914 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11915 q = 1) (hb : d112686 q = 1) : d142218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11973 q = 1) (hb : d112686 q = 1) : d142275 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11973, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11974 q = 1) (hb : d112686 q = 1) : d142276 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11974, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25958 (p : Pattern) (ha : d11980 p = 1) (hb : d112686 p = 1) : d142282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d112686 q = 1) : d142277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25957 q ha hb
    | true =>
      simp only [d11975, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d112686 q = 1) : d142278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d112686 q = 1) : d142279 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d112686 q = 1) : d142280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d112686 q = 1) : d142281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d112686 q = 1) : d142282 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25959 (p : Pattern) (ha : d5726 p = 1) (hb : d94753 p = 1) : d5237 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2069 q = 1) : d2069 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5726 q = 1) (hb : d94753 q = 1) : d5237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5726, d94753, d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5726, d94753, d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25960 (p : Pattern) (ha : d12013 p = 1) (hb : d112686 p = 1) : d142220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11912 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11913 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11914 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11915 q = 1) (hb : d112686 q = 1) : d142218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12008 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12008, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25959 q ha hb
    | true =>
      simp only [d12008, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12009 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12009, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12009, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12010 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12010, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12010, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12011 q = 1) (hb : d112686 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12011, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12011, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12012 q = 1) (hb : d112686 q = 1) : d142219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12012, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12013 q = 1) (hb : d112686 q = 1) : d142220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12013, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25961 (p : Pattern) (ha : d12019 p = 1) (hb : d112686 p = 1) : d142288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25960 q ha hb
    | true =>
      simp only [d12014, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d112686 q = 1) : d142285 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d112686 q = 1) : d142286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d112686 q = 1) : d142287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12019 q = 1) (hb : d112686 q = 1) : d142288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25962 (p : Pattern) (ha : d109027 p = 1) (hb : d112686 p = 1) : d142294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d112686 q = 1) : d142258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25953 q ha hb
    | true =>
      simp only [d11956, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25954 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d112686 q = 1) : d142259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d112686 q = 1) : d142260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d112686 q = 1) : d142261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d112686 q = 1) : d142268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25955 q ha hb
    | true =>
      simp only [d11966, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25956 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d112686 q = 1) : d142269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d112686 q = 1) : d142270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d112686 q = 1) : d142283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25958 q ha hb
    | true =>
      simp only [d11981, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25941 q ha hb
  have h9 (q : Pattern) (ha : d109023 q = 1) (hb : d112686 q = 1) : d142284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109023, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d112686 q = 1) : d142289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25961 q ha hb
    | true =>
      simp only [d12020, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d112686 q = 1) : d142290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109024 q = 1) (hb : d112686 q = 1) : d142291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109025 q = 1) (hb : d112686 q = 1) : d142292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109025, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109026 q = 1) (hb : d112686 q = 1) : d142293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109026, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109027 q = 1) (hb : d112686 q = 1) : d142294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25963 (p : Pattern) (ha : d12026 p = 1) (hb : d112686 p = 1) : d142295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d112686 q = 1) : d142228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d112686 q = 1) : d142254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12026 q = 1) (hb : d112686 q = 1) : d142295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12026, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25964 (p : Pattern) (ha : d12027 p = 1) (hb : d112686 p = 1) : d142296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d112686 q = 1) : d142232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d112686 q = 1) : d142256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12027 q = 1) (hb : d112686 q = 1) : d142296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12027, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12027, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25965 (p : Pattern) (ha : d12032 p = 1) (hb : d112686 p = 1) : d142301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d112686 q = 1) : d142227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d112686 q = 1) : d142262 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d112686 q = 1) : d142263 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12032 q = 1) (hb : d112686 q = 1) : d142301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12032, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25966 (p : Pattern) (ha : d12033 p = 1) (hb : d112686 p = 1) : d142302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d112686 q = 1) : d142225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25940 q ha hb
    | true =>
      simp only [d11923, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d112686 q = 1) : d142226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d112686 q = 1) : d142231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d112686 q = 1) : d142265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d112686 q = 1) : d142266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12033 q = 1) (hb : d112686 q = 1) : d142302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12033, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12033, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25967 (p : Pattern) (ha : d12037 p = 1) (hb : d112686 p = 1) : d142306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d112686 q = 1) : d142277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25957 q ha hb
    | true =>
      simp only [d11975, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d112686 q = 1) : d142278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25939 q ha hb
    | true =>
      simp only [d11919, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d112686 q = 1) : d142279 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d112686 q = 1) : d142280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d112686 q = 1) : d142281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d112686 q = 1) : d142306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25968 (p : Pattern) (ha : d12043 p = 1) (hb : d112686 p = 1) : d142309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d112686 q = 1) : d142221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25960 q ha hb
    | true =>
      simp only [d12014, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d112686 q = 1) : d142222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d112686 q = 1) : d142285 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d112686 q = 1) : d142286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d112686 q = 1) : d142287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12043 q = 1) (hb : d112686 q = 1) : d142309 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12043, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25969 (p : Pattern) (ha : d109032 p = 1) (hb : d112686 p = 1) : d142315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d112686 q = 1) : d142258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25953 q ha hb
    | true =>
      simp only [d11956, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25954 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d112686 q = 1) : d142259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d112686 q = 1) : d142260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d112686 q = 1) : d142261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d112686 q = 1) : d142268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25955 q ha hb
    | true =>
      simp only [d11966, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25956 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d112686 q = 1) : d142269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d112686 q = 1) : d142270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d112686 q = 1) : d142283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25958 q ha hb
    | true =>
      simp only [d11981, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25941 q ha hb
  have h9 (q : Pattern) (ha : d109023 q = 1) (hb : d112686 q = 1) : d142284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109023, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d112686 q = 1) : d142289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25961 q ha hb
    | true =>
      simp only [d12020, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d112686 q = 1) : d142290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109024 q = 1) (hb : d112686 q = 1) : d142291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109025 q = 1) (hb : d112686 q = 1) : d142292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109025, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109026 q = 1) (hb : d112686 q = 1) : d142293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109026, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12028 q = 1) (hb : d112686 q = 1) : d142297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25963 q ha hb
    | true =>
      simp only [d12028, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25964 q ha hb
  have h16 (q : Pattern) (ha : d12029 q = 1) (hb : d112686 q = 1) : d142298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12030 q = 1) (hb : d112686 q = 1) : d142299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12030, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12031 q = 1) (hb : d112686 q = 1) : d142300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12034 q = 1) (hb : d112686 q = 1) : d142303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25965 q ha hb
    | true =>
      simp only [d12034, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25966 q ha hb
  have h20 (q : Pattern) (ha : d12035 q = 1) (hb : d112686 q = 1) : d142304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12036 q = 1) (hb : d112686 q = 1) : d142305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12036, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12038 q = 1) (hb : d112686 q = 1) : d142307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25967 q ha hb
    | true =>
      simp only [d12038, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25944 q ha hb
  have h23 (q : Pattern) (ha : d109028 q = 1) (hb : d112686 q = 1) : d142308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109028, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12044 q = 1) (hb : d112686 q = 1) : d142310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25968 q ha hb
    | true =>
      simp only [d12044, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12045 q = 1) (hb : d112686 q = 1) : d142311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12045, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d109029 q = 1) (hb : d112686 q = 1) : d142312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d109029, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d109030 q = 1) (hb : d112686 q = 1) : d142313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109030, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d109031 q = 1) (hb : d112686 q = 1) : d142314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109031, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d109032 q = 1) (hb : d112686 q = 1) : d142315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109032, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25970 (p : Pattern) (ha : d109039 p = 1) (hb : d112686 p = 1) : d142335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d112686 q = 1) : d142307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25967 q ha hb
    | true =>
      simp only [d12038, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25944 q ha hb
  have h2 (q : Pattern) (ha : d109028 q = 1) (hb : d112686 q = 1) : d142308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109028, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12044 q = 1) (hb : d112686 q = 1) : d142310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25968 q ha hb
    | true =>
      simp only [d12044, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12045 q = 1) (hb : d112686 q = 1) : d142311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12045, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d112686 q = 1) : d142312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109029, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d112686 q = 1) : d142333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d112686 q = 1) : d142334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d112686 q = 1) : d142335 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25971 (p : Pattern) (ha : d12089 p = 1) (hb : d112686 p = 1) : d142349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12077 q = 1) (hb : d112686 q = 1) : d142343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d112686, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18504 q ha hb
    | true =>
      simp only [d12077, d112686, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12078 q = 1) (hb : d112686 q = 1) : d142344 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12078, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12079 q = 1) (hb : d112686 q = 1) : d142345 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12079, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12080 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12081 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12082 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12083 q = 1) (hb : d112686 q = 1) : d142346 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12083, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12084 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12085 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12086 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12087 q = 1) (hb : d112686 q = 1) : d142347 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12088 q = 1) (hb : d112686 q = 1) : d142348 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12088, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12089 q = 1) (hb : d112686 q = 1) : d142349 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12089, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25972 (p : Pattern) (ha : d12094 p = 1) (hb : d112686 p = 1) : d142353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12084 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12085 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12086 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12087 q = 1) (hb : d112686 q = 1) : d142347 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12092 q = 1) (hb : d112686 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12092, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12093 q = 1) (hb : d112686 q = 1) : d142352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12093, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12094 q = 1) (hb : d112686 q = 1) : d142353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12094, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro25973 (p : Pattern) (ha : d12100 p = 1) (hb : d112686 p = 1) : d142359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d112686 q = 1) : d142350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25971 q ha hb
    | true =>
      simp only [d12090, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d112686 q = 1) : d142351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12095 q = 1) (hb : d112686 q = 1) : d142354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25972 q ha hb
    | true =>
      simp only [d12095, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12096 q = 1) (hb : d112686 q = 1) : d142355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12097 q = 1) (hb : d112686 q = 1) : d142356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d112686 q = 1) : d142357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12098, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d112686 q = 1) : d142358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d112686 q = 1) : d142359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25974 (p : Pattern) (ha : d12108 p = 1) (hb : d112686 p = 1) : d142367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d112686 q = 1) : d142354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25972 q ha hb
    | true =>
      simp only [d12095, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d112686 q = 1) : d142355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12103 q = 1) (hb : d112686 q = 1) : d142362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25950 q ha hb
    | true =>
      simp only [d12103, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12104 q = 1) (hb : d112686 q = 1) : d142363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12105 q = 1) (hb : d112686 q = 1) : d142364 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12106 q = 1) (hb : d112686 q = 1) : d142365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12106, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12107 q = 1) (hb : d112686 q = 1) : d142366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12107, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12108 q = 1) (hb : d112686 q = 1) : d142367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12108, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25975 (p : Pattern) (ha : d5770 p = 1) (hb : d94753 p = 1) : d6642 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2350 q = 1) : d2350 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5770 q = 1) (hb : d94753 q = 1) : d6642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5770, d94753, d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5770, d94753, d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro25976 (p : Pattern) (ha : d12141 p = 1) (hb : d112686 p = 1) : d142353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12084 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12085 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12086 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12087 q = 1) (hb : d112686 q = 1) : d142347 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12136 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12136, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25975 q ha hb
    | true =>
      simp only [d12136, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12137 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12137, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12137, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12138 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12138, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12138, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12139 q = 1) (hb : d112686 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12139, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12139, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12140 q = 1) (hb : d112686 q = 1) : d142352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12140, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12141 q = 1) (hb : d112686 q = 1) : d142353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12141, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro25977 (p : Pattern) (ha : d12147 p = 1) (hb : d112686 p = 1) : d142373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d112686 q = 1) : d142354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25976 q ha hb
    | true =>
      simp only [d12142, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d112686 q = 1) : d142355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12144 q = 1) (hb : d112686 q = 1) : d142370 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12145 q = 1) (hb : d112686 q = 1) : d142371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12145, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12146 q = 1) (hb : d112686 q = 1) : d142372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12146, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12147 q = 1) (hb : d112686 q = 1) : d142373 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12147, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25978 (p : Pattern) (ha : d109049 p = 1) (hb : d112686 p = 1) : d142379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d112686 q = 1) : d142368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25973 q ha hb
    | true =>
      simp only [d12109, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25974 q ha hb
  have h2 (q : Pattern) (ha : d109045 q = 1) (hb : d112686 q = 1) : d142369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109045, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12148 q = 1) (hb : d112686 q = 1) : d142374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25977 q ha hb
    | true =>
      simp only [d12148, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12149 q = 1) (hb : d112686 q = 1) : d142375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12149, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d112686 q = 1) : d142376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109046, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d112686 q = 1) : d142377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d112686 q = 1) : d142378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d112686 q = 1) : d142379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25979 (p : Pattern) (ha : d109055 p = 1) (hb : d112686 p = 1) : d142396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d112686 q = 1) : d142241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25943 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d112686 q = 1) : d142242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d112686 q = 1) : d142251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25943 q ha hb
    | true =>
      simp only [d11949, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25946 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d112686 q = 1) : d142252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d112686 q = 1) : d142253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109033 q = 1) (hb : d112686 q = 1) : d142316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25962 q ha hb
    | true =>
      simp only [d109033, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25969 q ha hb
  have h7 (q : Pattern) (ha : d12063 q = 1) (hb : d112686 q = 1) : d142329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25947 q ha hb
    | true =>
      simp only [d12063, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25948 q ha hb
  have h8 (q : Pattern) (ha : d109034 q = 1) (hb : d112686 q = 1) : d142330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109034, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109035 q = 1) (hb : d112686 q = 1) : d142331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109035, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d109036 q = 1) (hb : d112686 q = 1) : d142332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109036, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109040 q = 1) (hb : d112686 q = 1) : d142336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109040, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25970 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d112686 q = 1) : d142338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25949 q ha hb
  have h13 (q : Pattern) (ha : d109041 q = 1) (hb : d112686 q = 1) : d142339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109041, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109042 q = 1) (hb : d112686 q = 1) : d142340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109042, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109043 q = 1) (hb : d112686 q = 1) : d142341 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109043, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109044 q = 1) (hb : d112686 q = 1) : d142342 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109044, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109050 q = 1) (hb : d112686 q = 1) : d142380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109050, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25978 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d112686 q = 1) : d142391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25952 q ha hb
  have h19 (q : Pattern) (ha : d109051 q = 1) (hb : d112686 q = 1) : d142392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109051, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d109052 q = 1) (hb : d112686 q = 1) : d142393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109052, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d109053 q = 1) (hb : d112686 q = 1) : d142394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109053, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109054 q = 1) (hb : d112686 q = 1) : d142395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109054, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109055 q = 1) (hb : d112686 q = 1) : d142396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109055, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25980 (p : Pattern) (ha : d109061 p = 1) (hb : d112686 p = 1) : d142402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d112686 q = 1) : d142397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25979 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d112686 q = 1) : d142398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d112686 q = 1) : d142399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d112686 q = 1) : d142400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d112686 q = 1) : d142401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d112686 q = 1) : d142402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25981 (p : Pattern) (ha : d109067 p = 1) (hb : d112686 p = 1) : d142408 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d112686 q = 1) : d141653 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25774 q ha hb
    | true =>
      simp only [d108896, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25812 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d112686 q = 1) : d141839 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25854 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d112686 q = 1) : d141840 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d112686 q = 1) : d142026 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25896 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d112686 q = 1) : d142027 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d112686 q = 1) : d142028 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d112686 q = 1) : d142214 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25938 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d112686 q = 1) : d142215 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d112686 q = 1) : d142216 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d112686 q = 1) : d142217 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d112686 q = 1) : d142403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25980 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d112686 q = 1) : d142404 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d112686 q = 1) : d142405 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d112686 q = 1) : d142406 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d112686 q = 1) : d142407 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d112686 q = 1) : d142408 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro25982 (p : Pattern) (ha : d109073 p = 1) (hb : d112686 p = 1) : d142414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d112686 q = 1) : d142409 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25981 q ha hb
    | true =>
      simp only [d109068, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d112686 q = 1) : d142410 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d112686 q = 1) : d142411 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d112686 q = 1) : d142412 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d112686 q = 1) : d142413 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d112686 q = 1) : d142414 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25983 (p : Pattern) (ha : d109079 p = 1) (hb : d112686 p = 1) : d142420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d112686 q = 1) : d142415 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25982 q ha hb
    | true =>
      simp only [d109074, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d112686 q = 1) : d142416 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d112686 q = 1) : d142417 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d112686 q = 1) : d142418 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d112686 q = 1) : d142419 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d112686 q = 1) : d142420 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25984 (p : Pattern) (ha : d109085 p = 1) (hb : d112686 p = 1) : d142426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d112686 q = 1) : d142421 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25983 q ha hb
    | true =>
      simp only [d109080, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d112686 q = 1) : d142422 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d112686 q = 1) : d142423 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d112686 q = 1) : d142424 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d112686 q = 1) : d142425 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d112686 q = 1) : d142426 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25985 (p : Pattern) (ha : d109091 p = 1) (hb : d112686 p = 1) : d142432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d112686 q = 1) : d142427 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25984 q ha hb
    | true =>
      simp only [d109086, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d112686 q = 1) : d142428 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d112686 q = 1) : d142429 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d112686 q = 1) : d142430 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d112686 q = 1) : d142431 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d112686 q = 1) : d142432 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25986 (p : Pattern) (ha : d109097 p = 1) (hb : d112686 p = 1) : d142438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d112686 q = 1) : d142433 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25985 q ha hb
    | true =>
      simp only [d109092, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d112686 q = 1) : d142434 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d112686 q = 1) : d142435 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d112686 q = 1) : d142436 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d112686 q = 1) : d142437 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d112686 q = 1) : d142438 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25987 (p : Pattern) (ha : d109103 p = 1) (hb : d112686 p = 1) : d142444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d112686 q = 1) : d142439 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25986 q ha hb
    | true =>
      simp only [d109098, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d112686 q = 1) : d142440 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d112686 q = 1) : d142441 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d112686 q = 1) : d142442 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d112686 q = 1) : d142443 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d112686 q = 1) : d142444 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25988 (p : Pattern) (ha : d109109 p = 1) (hb : d112686 p = 1) : d142450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d112686 q = 1) : d142445 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25987 q ha hb
    | true =>
      simp only [d109104, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d112686 q = 1) : d142446 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d112686 q = 1) : d142447 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d112686 q = 1) : d142448 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d112686 q = 1) : d142449 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d112686 q = 1) : d142450 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25989 (p : Pattern) (ha : d112691 p = 1) (hb : d141304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112689 q = 1) (hb : d141302 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112689, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112689, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d112690 q = 1) (hb : d141303 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112690, d141303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112690, d141303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112691 q = 1) (hb : d141304 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112691, d141304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112691, d141304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25990 (p : Pattern) (ha : d112697 p = 1) (hb : d141310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112696 q = 1) (hb : d141309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112696, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112696, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112697 q = 1) (hb : d141310 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112697, d141310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112697, d141310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25991 (p : Pattern) (ha : d112703 p = 1) (hb : d141316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d141312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112699, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d141313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d141314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d141315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112703 q = 1) (hb : d141316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112703, d141316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112703, d141316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro25992 (p : Pattern) (ha : d112704 p = 1) (hb : d141317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112696 q = 1) (hb : d141309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112696, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112696, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112704 q = 1) (hb : d141317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112704, d141317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112704, d141317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25993 (p : Pattern) (ha : d112710 p = 1) (hb : d141323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112699 q = 1) (hb : d141312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112699, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112699, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d112700 q = 1) (hb : d141313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112700, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112700, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112701 q = 1) (hb : d141314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112701, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d112701, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112702 q = 1) (hb : d141315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112702, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112702, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d112705 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
    | true =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112706 q = 1) (hb : d141319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112706, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d112707 q = 1) (hb : d141320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112707, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d112708 q = 1) (hb : d141321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112708, d141321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d112708, d141321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112709 q = 1) (hb : d141322 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112709, d141322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d112709, d141322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112710 q = 1) (hb : d141323 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112710, d141323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112710, d141323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro25994 (p : Pattern) (ha : d112717 p = 1) (hb : d141330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112705 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
    | true =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112706 q = 1) (hb : d141319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112706, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112706, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112707 q = 1) (hb : d141320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112707, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112707, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112715 q = 1) (hb : d141328 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112715, d141328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112715, d141328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112716 q = 1) (hb : d141329 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112716, d141329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112716, d141329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112717 q = 1) (hb : d141330 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112717, d141330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112717, d141330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25995 (p : Pattern) (ha : d112725 p = 1) (hb : d141338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112723 q = 1) (hb : d141336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112723, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112723, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d112724 q = 1) (hb : d141337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112724, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112724, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112725 q = 1) (hb : d141338 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112725, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112725, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25996 (p : Pattern) (ha : d112731 p = 1) (hb : d141344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112726 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25995 q ha hb
    | true =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112727 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112728 q = 1) (hb : d141341 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112728, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112728, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112729 q = 1) (hb : d141342 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112729, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112729, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112730 q = 1) (hb : d141343 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112730, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112730, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112731 q = 1) (hb : d141344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112731, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112731, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25997 (p : Pattern) (ha : d112737 p = 1) (hb : d141350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112732 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112732, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25996 q ha hb
    | true =>
      simp only [d112732, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112733 q = 1) (hb : d141346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112733, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112733, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d112734 q = 1) (hb : d141347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112734, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112734, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112735 q = 1) (hb : d141348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112735, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112735, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112736 q = 1) (hb : d141349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112736, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112736, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112737 q = 1) (hb : d141350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112737, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112737, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25998 (p : Pattern) (ha : d112743 p = 1) (hb : d141356 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d112711 q = 1) (hb : d141324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112711, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25991 q ha hb
    | true =>
      simp only [d112711, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25993 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d112712 q = 1) (hb : d141325 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112712, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112712, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d112713 q = 1) (hb : d141326 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112713, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112713, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112714 q = 1) (hb : d141327 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112714, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112714, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112718 q = 1) (hb : d141331 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112718, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112718, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25994 q ha hb
  have h12 (q : Pattern) (ha : d112719 q = 1) (hb : d141332 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112719, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112719, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112720 q = 1) (hb : d141333 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112720, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112720, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112721 q = 1) (hb : d141334 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112721, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112721, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112722 q = 1) (hb : d141335 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112722, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112722, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112738 q = 1) (hb : d141351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112738, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112738, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25997 q ha hb
  have h17 (q : Pattern) (ha : d112739 q = 1) (hb : d141352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112739, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112739, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d112740 q = 1) (hb : d141353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112740, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112740, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112741 q = 1) (hb : d141354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112741, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d112741, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d112742 q = 1) (hb : d141355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112742, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112742, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112743 q = 1) (hb : d141356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112743, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112743, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25999 (p : Pattern) (ha : d112753 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112753 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112753, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112753, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
