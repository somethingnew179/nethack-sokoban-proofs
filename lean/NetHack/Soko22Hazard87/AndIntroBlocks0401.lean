import NetHack.Soko22Hazard87.AndIntroBlocks0400
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro100250 (p : Pattern) (ha : d363281 p = 1) (hb : d363639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362505 q = 1) (hb : d363634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d362505, d363634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362505, d363634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100249 q ha hb
  have h4 (q : Pattern) (ha : d362506 q = 1) (hb : d363635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d362506, d363635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362506, d363635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362507 q = 1) (hb : d363636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d362507, d363636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362507, d363636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362507 q = 1) (hb : d363637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363280 q = 1) (hb : d363638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363280, d363638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363280, d363638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d363281 q = 1) (hb : d363639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363281, d363639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363281, d363639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100251 (p : Pattern) (ha : d363287 p = 1) (hb : d363645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363282 q = 1) (hb : d363640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363282, d363640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100250 q ha hb
    | true =>
      simp only [d363282, d363640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363283 q = 1) (hb : d363641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363283, d363641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363283, d363641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363284 q = 1) (hb : d363642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363284, d363642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363284, d363642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363285 q = 1) (hb : d363643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363285, d363643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363285, d363643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363286 q = 1) (hb : d363644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363286, d363644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363286, d363644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363287 q = 1) (hb : d363645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363287, d363645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363287, d363645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100252 (p : Pattern) (ha : d363293 p = 1) (hb : d363651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363288 q = 1) (hb : d363646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363288, d363646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100251 q ha hb
    | true =>
      simp only [d363288, d363646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363289 q = 1) (hb : d363647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363289, d363647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363289, d363647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363290 q = 1) (hb : d363648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363290, d363648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363290, d363648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363291 q = 1) (hb : d363649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363291, d363649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363291, d363649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363292 q = 1) (hb : d363650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363292, d363650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363292, d363650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363293 q = 1) (hb : d363651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363293, d363651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363293, d363651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100253 (p : Pattern) (ha : d363299 p = 1) (hb : d363657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363294 q = 1) (hb : d363652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363294, d363652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100252 q ha hb
    | true =>
      simp only [d363294, d363652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363295 q = 1) (hb : d363653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363295, d363653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363295, d363653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363296 q = 1) (hb : d363654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363296, d363654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363296, d363654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363297 q = 1) (hb : d363655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363297, d363655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363297, d363655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363298 q = 1) (hb : d363656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363298, d363656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363298, d363656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363299 q = 1) (hb : d363657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363299, d363657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363299, d363657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100254 (p : Pattern) (ha : d363305 p = 1) (hb : d363663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363300 q = 1) (hb : d363658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363300, d363658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100253 q ha hb
    | true =>
      simp only [d363300, d363658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363301 q = 1) (hb : d363659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363301, d363659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363301, d363659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363302 q = 1) (hb : d363660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363302, d363660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363302, d363660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363303 q = 1) (hb : d363661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363303, d363661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363303, d363661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363304 q = 1) (hb : d363662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363304, d363662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363304, d363662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363305 q = 1) (hb : d363663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363305, d363663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363305, d363663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100255 (p : Pattern) (ha : d363311 p = 1) (hb : d363669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363306 q = 1) (hb : d363664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363306, d363664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100254 q ha hb
    | true =>
      simp only [d363306, d363664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363307 q = 1) (hb : d363665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363307, d363665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363307, d363665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363308 q = 1) (hb : d363666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363308, d363666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363308, d363666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363309 q = 1) (hb : d363667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363309, d363667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363309, d363667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363310 q = 1) (hb : d363668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363310, d363668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363310, d363668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363311 q = 1) (hb : d363669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363311, d363669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363311, d363669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100256 (p : Pattern) (ha : d363317 p = 1) (hb : d363675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363312 q = 1) (hb : d363670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363312, d363670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100255 q ha hb
    | true =>
      simp only [d363312, d363670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363313 q = 1) (hb : d363671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363313, d363671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363313, d363671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363314 q = 1) (hb : d363672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363314, d363672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363314, d363672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363315 q = 1) (hb : d363673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363315, d363673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363315, d363673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363316 q = 1) (hb : d363674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363316, d363674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363316, d363674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363317 q = 1) (hb : d363675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363317, d363675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363317, d363675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100257 (p : Pattern) (ha : d363323 p = 1) (hb : d363681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363318 q = 1) (hb : d363676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363318, d363676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100256 q ha hb
    | true =>
      simp only [d363318, d363676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363319 q = 1) (hb : d363677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363319, d363677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363319, d363677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363320 q = 1) (hb : d363678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363320, d363678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363320, d363678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363321 q = 1) (hb : d363679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363321, d363679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363321, d363679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363322 q = 1) (hb : d363680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363322, d363680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363322, d363680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363323 q = 1) (hb : d363681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363323, d363681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363323, d363681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100258 (p : Pattern) (ha : d308 p = 1) (hb : d357527 p = 1) : d363684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43964 q = 1) : d363400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43964, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100121 q ha hb
    | true =>
      simp only [d43964, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100122 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43965 q = 1) : d363401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43965, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43965, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43966 q = 1) : d363402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43966, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43966, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43967 q = 1) : d363403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43967, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43967, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43968 q = 1) : d363404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43968, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43968, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357527 q = 1) : d363684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357527, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357527, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100259 (p : Pattern) (ha : d308 p = 1) (hb : d357538 p = 1) : d363695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357533 q = 1) : d363690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357533, d363690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100162 q ha hb
    | true =>
      simp only [d357533, d363690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100130 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357534 q = 1) : d363691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357534, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357534, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357535 q = 1) : d363692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357535, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357535, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357536 q = 1) : d363693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357536, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357536, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357537 q = 1) : d363694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357537, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357537, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357538 q = 1) : d363695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357538, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357538, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100260 (p : Pattern) (ha : d308 p = 1) (hb : d357544 p = 1) : d363701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43970 q = 1) : d363406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43970, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100120 q ha hb
    | true =>
      simp only [d43970, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100123 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43971 q = 1) : d363407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43971, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43971, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357525 q = 1) : d363682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357525, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357525, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357526 q = 1) : d363683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357526, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357526, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357528 q = 1) : d363685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357528, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357528, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100258 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357529 q = 1) : d363686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357529, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357529, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d357530 q = 1) : d363687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357530, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357530, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d357531 q = 1) : d363688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357531, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357531, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d357532 q = 1) : d363689 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357532, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357532, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d357539 q = 1) : d363696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357539, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357539, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100259 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d357540 q = 1) : d363697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357540, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357540, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d357541 q = 1) : d363698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357541, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357541, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d357542 q = 1) : d363699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357542, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357542, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d357543 q = 1) : d363700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357543, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357543, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d357544 q = 1) : d363701 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357544, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357544, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100261 (p : Pattern) (ha : d308 p = 1) (hb : d357550 p = 1) : d363707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357545 q = 1) : d363702 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357545, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357545, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100260 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357546 q = 1) : d363703 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357546, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357546, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357547 q = 1) : d363704 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357547, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357547, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357548 q = 1) : d363705 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357548, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357548, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357549 q = 1) : d363706 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357549, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357549, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357550 q = 1) : d363707 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357550, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357550, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100262 (p : Pattern) (ha : d357556 p = 1) (hb : d363232 p = 1) : d363713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357551 q = 1) : d363708 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357551, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357551, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100261 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357552 q = 1) : d363709 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357552, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357552, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357553 q = 1) : d363710 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357553, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357553, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d357554 q = 1) (hb : d363231 q = 1) : d363711 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d363231, d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357554, d363231, d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357555 q = 1) (hb : d363232 q = 1) : d363712 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d363232, d363712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357555, d363232, d363712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357556 q = 1) (hb : d363232 q = 1) : d363713 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d363713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357556, d363713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100263 (p : Pattern) (ha : d357562 p = 1) (hb : d363232 p = 1) : d363719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d363232 q = 1) : d363714 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d363714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100262 q ha hb
    | true =>
      simp only [d357557, d363714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d363232 q = 1) : d363715 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d363715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d363715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d363232 q = 1) : d363716 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d363716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d363716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d363232 q = 1) : d363717 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d363717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d363717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d363232 q = 1) : d363718 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d363718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d363718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d363232 q = 1) : d363719 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d363719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d363719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100264 (p : Pattern) (ha : d357568 p = 1) (hb : d363235 p = 1) : d363725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d363232 q = 1) : d363720 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d363720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100263 q ha hb
    | true =>
      simp only [d357563, d363720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d363232 q = 1) : d363721 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d363721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d363721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357565 q = 1) (hb : d363233 q = 1) : d363722 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d363233, d363722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d363233, d363722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d357566 q = 1) (hb : d363234 q = 1) : d363723 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d363234, d363723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357566, d363234, d363723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d357567 q = 1) (hb : d363235 q = 1) : d363724 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d363235, d363724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357567, d363235, d363724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d357568 q = 1) (hb : d363235 q = 1) : d363725 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d363725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357568, d363725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100265 (p : Pattern) (ha : d357574 p = 1) (hb : d363235 p = 1) : d363731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d363235 q = 1) : d363726 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d363726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100264 q ha hb
    | true =>
      simp only [d357569, d363726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d363235 q = 1) : d363727 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d363727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d363727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d363235 q = 1) : d363728 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d363728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d363728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d363235 q = 1) : d363729 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d363729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d363729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d363235 q = 1) : d363730 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d363730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d363730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d363235 q = 1) : d363731 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d363731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d363731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100266 (p : Pattern) (ha : d357580 p = 1) (hb : d363235 p = 1) : d363737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d363235 q = 1) : d363732 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d363732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100265 q ha hb
    | true =>
      simp only [d357575, d363732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d363235 q = 1) : d363733 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d363733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d363733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d363235 q = 1) : d363734 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d363734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d363734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d363235 q = 1) : d363735 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d363735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d363735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d363235 q = 1) : d363736 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d363736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d363736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d363235 q = 1) : d363737 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d363737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d363737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100267 (p : Pattern) (ha : d357586 p = 1) (hb : d363235 p = 1) : d363743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d363235 q = 1) : d363738 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d363738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100266 q ha hb
    | true =>
      simp only [d357581, d363738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d363235 q = 1) : d363739 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d363739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d363739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d363235 q = 1) : d363740 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d363740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d363740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d363235 q = 1) : d363741 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d363741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d363741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d363235 q = 1) : d363742 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d363742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d363742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d363235 q = 1) : d363743 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d363743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d363743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100268 (p : Pattern) (ha : d357592 p = 1) (hb : d363235 p = 1) : d363749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d363235 q = 1) : d363744 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d363744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100267 q ha hb
    | true =>
      simp only [d357587, d363744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d363235 q = 1) : d363745 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d363745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d363745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d363235 q = 1) : d363746 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d363746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d363746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d363235 q = 1) : d363747 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d363747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d363747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d363235 q = 1) : d363748 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d363748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d363748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d363235 q = 1) : d363749 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d363749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d363749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100269 (p : Pattern) (ha : d357598 p = 1) (hb : d363235 p = 1) : d363755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d363235 q = 1) : d363750 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d363750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100268 q ha hb
    | true =>
      simp only [d357593, d363750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d363235 q = 1) : d363751 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d363751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d363751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d363235 q = 1) : d363752 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d363752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d363752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d363235 q = 1) : d363753 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d363753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d363753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d363235 q = 1) : d363754 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d363754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d363754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d363235 q = 1) : d363755 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d363755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d363755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100270 (p : Pattern) (ha : d362318 p = 1) (hb : d363395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362232 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362241 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d362298 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d362206 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
    | true =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
  have h5 (q : Pattern) (ha : d362299 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362299, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d362299, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d362314 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d362315 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362315, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362315, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362316 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362316, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362316, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362317 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362317, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362317, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362318 q = 1) (hb : d363395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362318, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362318, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100271 (p : Pattern) (ha : d362339 p = 1) (hb : d363405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362241 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362206 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100198 q ha hb
    | true =>
      simp only [d362206, d363390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100199 q ha hb
  have h4 (q : Pattern) (ha : d362299 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362299, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362299, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d362314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d362315 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362315, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362315, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d362316 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362316, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362316, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362317 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362317, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362317, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d362324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d362329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d362331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d362216 q = 1) (hb : d363400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100201 q ha hb
    | true =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100202 q ha hb
  have h13 (q : Pattern) (ha : d362332 q = 1) (hb : d363401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362332, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d362332, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d362335 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d362336 q = 1) (hb : d363402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362336, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362336, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d362337 q = 1) (hb : d363403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362337, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d362337, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362338 q = 1) (hb : d363404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362338, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d362338, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d362339 q = 1) (hb : d363405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362339, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362339, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100272 (p : Pattern) (ha : d362359 p = 1) (hb : d363684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d362216 q = 1) (hb : d363400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100201 q ha hb
    | true =>
      simp only [d362216, d363400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100202 q ha hb
  have h3 (q : Pattern) (ha : d362332 q = 1) (hb : d363401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362332, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362332, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d362335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362336 q = 1) (hb : d363402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362336, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362336, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362357 q = 1) (hb : d363403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362357, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362357, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362358 q = 1) (hb : d363404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362358, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362358, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362359 q = 1) (hb : d363684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362359, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362359, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100273 (p : Pattern) (ha : d362485 p = 1) (hb : d363695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362460 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d362465 q = 1) (hb : d363690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362465, d363690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100241 q ha hb
    | true =>
      simp only [d362465, d363690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100246 q ha hb
  have h3 (q : Pattern) (ha : d362466 q = 1) (hb : d363691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362466, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362466, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d362481 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362482 q = 1) (hb : d363692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362482, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362482, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362483 q = 1) (hb : d363693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362483, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362483, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362484 q = 1) (hb : d363694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362484, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362484, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362485 q = 1) (hb : d363695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362485, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362485, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100274 (p : Pattern) (ha : d362498 p = 1) (hb : d363701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362224 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362340 q = 1) (hb : d363406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362340, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100270 q ha hb
    | true =>
      simp only [d362340, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100271 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362353 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362354 q = 1) (hb : d363407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362354, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362354, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362355 q = 1) (hb : d363682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362355, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362355, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362356 q = 1) (hb : d363683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362356, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362356, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362360 q = 1) (hb : d363685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362360, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362360, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100272 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d362362 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d362363 q = 1) (hb : d363686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362363, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362363, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d362364 q = 1) (hb : d363687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362364, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362364, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d362365 q = 1) (hb : d363688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362365, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362365, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d362366 q = 1) (hb : d363689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362366, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362366, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362486 q = 1) (hb : d363696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362486, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362486, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100273 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d362493 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d362494 q = 1) (hb : d363697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362494, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362494, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d362495 q = 1) (hb : d363698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362495, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362495, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d362496 q = 1) (hb : d363699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362496, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362496, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d362497 q = 1) (hb : d363700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362497, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d362497, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d362498 q = 1) (hb : d363701 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d362498, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362498, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100275 (p : Pattern) (ha : d362504 p = 1) (hb : d363707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362499 q = 1) (hb : d363702 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d362499, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362499, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100274 q ha hb
  have h2 (q : Pattern) (ha : d362500 q = 1) (hb : d363703 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d362500, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362500, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362501 q = 1) (hb : d363704 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d362501, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362501, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362502 q = 1) (hb : d363705 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d362502, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362502, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362503 q = 1) (hb : d363706 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d362503, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362503, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362504 q = 1) (hb : d363707 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d362504, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362504, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100276 (p : Pattern) (ha : d363281 p = 1) (hb : d363713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362505 q = 1) (hb : d363708 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d362505, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362505, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100275 q ha hb
  have h4 (q : Pattern) (ha : d362506 q = 1) (hb : d363709 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d362506, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362506, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362507 q = 1) (hb : d363710 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d362507, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362507, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362507 q = 1) (hb : d363711 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363280 q = 1) (hb : d363712 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363280, d363712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363280, d363712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d363281 q = 1) (hb : d363713 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363281, d363713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363281, d363713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100277 (p : Pattern) (ha : d363287 p = 1) (hb : d363719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363282 q = 1) (hb : d363714 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363282, d363714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100276 q ha hb
    | true =>
      simp only [d363282, d363714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363283 q = 1) (hb : d363715 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363283, d363715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363283, d363715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363284 q = 1) (hb : d363716 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363284, d363716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363284, d363716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363285 q = 1) (hb : d363717 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363285, d363717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363285, d363717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363286 q = 1) (hb : d363718 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363286, d363718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363286, d363718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363287 q = 1) (hb : d363719 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363287, d363719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363287, d363719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100278 (p : Pattern) (ha : d363293 p = 1) (hb : d363725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363288 q = 1) (hb : d363720 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363288, d363720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100277 q ha hb
    | true =>
      simp only [d363288, d363720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363289 q = 1) (hb : d363721 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363289, d363721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363289, d363721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363290 q = 1) (hb : d363722 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363290, d363722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363290, d363722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363291 q = 1) (hb : d363723 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363291, d363723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363291, d363723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363292 q = 1) (hb : d363724 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363292, d363724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363292, d363724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363293 q = 1) (hb : d363725 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363293, d363725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363293, d363725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100279 (p : Pattern) (ha : d363299 p = 1) (hb : d363731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363294 q = 1) (hb : d363726 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363294, d363726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100278 q ha hb
    | true =>
      simp only [d363294, d363726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363295 q = 1) (hb : d363727 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363295, d363727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363295, d363727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363296 q = 1) (hb : d363728 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363296, d363728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363296, d363728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363297 q = 1) (hb : d363729 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363297, d363729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363297, d363729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363298 q = 1) (hb : d363730 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363298, d363730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363298, d363730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363299 q = 1) (hb : d363731 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363299, d363731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363299, d363731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100280 (p : Pattern) (ha : d363305 p = 1) (hb : d363737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363300 q = 1) (hb : d363732 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363300, d363732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100279 q ha hb
    | true =>
      simp only [d363300, d363732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363301 q = 1) (hb : d363733 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363301, d363733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363301, d363733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363302 q = 1) (hb : d363734 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363302, d363734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363302, d363734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363303 q = 1) (hb : d363735 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363303, d363735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363303, d363735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363304 q = 1) (hb : d363736 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363304, d363736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363304, d363736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363305 q = 1) (hb : d363737 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363305, d363737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363305, d363737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100281 (p : Pattern) (ha : d363311 p = 1) (hb : d363743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363306 q = 1) (hb : d363738 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363306, d363738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100280 q ha hb
    | true =>
      simp only [d363306, d363738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363307 q = 1) (hb : d363739 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363307, d363739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363307, d363739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363308 q = 1) (hb : d363740 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363308, d363740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363308, d363740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363309 q = 1) (hb : d363741 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363309, d363741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363309, d363741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363310 q = 1) (hb : d363742 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363310, d363742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363310, d363742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363311 q = 1) (hb : d363743 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363311, d363743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363311, d363743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100282 (p : Pattern) (ha : d363317 p = 1) (hb : d363749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363312 q = 1) (hb : d363744 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363312, d363744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100281 q ha hb
    | true =>
      simp only [d363312, d363744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363313 q = 1) (hb : d363745 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363313, d363745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363313, d363745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363314 q = 1) (hb : d363746 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363314, d363746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363314, d363746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363315 q = 1) (hb : d363747 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363315, d363747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363315, d363747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363316 q = 1) (hb : d363748 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363316, d363748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363316, d363748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363317 q = 1) (hb : d363749 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363317, d363749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363317, d363749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100283 (p : Pattern) (ha : d363323 p = 1) (hb : d363755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363318 q = 1) (hb : d363750 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363318, d363750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100282 q ha hb
    | true =>
      simp only [d363318, d363750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363319 q = 1) (hb : d363751 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363319, d363751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363319, d363751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363320 q = 1) (hb : d363752 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363320, d363752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363320, d363752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363321 q = 1) (hb : d363753 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363321, d363753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363321, d363753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363322 q = 1) (hb : d363754 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363322, d363754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363322, d363754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363323 q = 1) (hb : d363755 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363323, d363755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363323, d363755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100284 (p : Pattern) (ha : d363097 p = 1) (hb : d363395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d360341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363093 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363093, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d363093, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d360483 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d363094 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363094, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363094, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d363095 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363095, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363095, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d363096 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363096, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363096, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d363097 q = 1) (hb : d363395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363097, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363097, d363395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100285 (p : Pattern) (ha : d363102 p = 1) (hb : d363405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d360275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360341 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d363390 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d363093 q = 1) (hb : d363391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363093, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363093, d363391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d360483 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d363094 q = 1) (hb : d363392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363094, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363094, d363392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d363095 q = 1) (hb : d363393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363095, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363095, d363393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363096 q = 1) (hb : d363394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363096, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363096, d363394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d360493 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d360498 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d360500 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d363400 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d363098 q = 1) (hb : d363401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363098, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d363098, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d360507 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363099 q = 1) (hb : d363402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363099, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363099, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363100 q = 1) (hb : d363403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363100, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d363100, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d363101 q = 1) (hb : d363404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363101, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d363101, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d363102 q = 1) (hb : d363405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363102, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d363102, d363405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100286 (p : Pattern) (ha : d363109 p = 1) (hb : d363684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d363400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363098 q = 1) (hb : d363401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363098, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363098, d363401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d360507 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363099 q = 1) (hb : d363402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363099, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363099, d363402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363107 q = 1) (hb : d363403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363107, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363107, d363403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363108 q = 1) (hb : d363404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363108, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363108, d363404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363109 q = 1) (hb : d363684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363109, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363109, d363684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100287 (p : Pattern) (ha : d363119 p = 1) (hb : d363695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d363690 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363115 q = 1) (hb : d363691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363115, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363115, d363691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d360710 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363116 q = 1) (hb : d363692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363116, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363116, d363692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363117 q = 1) (hb : d363693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363117, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363117, d363693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363118 q = 1) (hb : d363694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363118, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363118, d363694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363119 q = 1) (hb : d363695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363119, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363119, d363695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100288 (p : Pattern) (ha : d363125 p = 1) (hb : d363701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d360267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363103 q = 1) (hb : d363406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363103, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100284 q ha hb
    | true =>
      simp only [d363103, d363406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100285 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d360525 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363104 q = 1) (hb : d363407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363104, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363104, d363407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363105 q = 1) (hb : d363682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363105, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363105, d363682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363106 q = 1) (hb : d363683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363106, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363106, d363683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363110 q = 1) (hb : d363685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363110, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363110, d363685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100286 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d360534 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d363111 q = 1) (hb : d363686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363111, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363111, d363686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d363112 q = 1) (hb : d363687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363112, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d363112, d363687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d363113 q = 1) (hb : d363688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363113, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d363113, d363688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d363114 q = 1) (hb : d363689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363114, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363114, d363689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d363120 q = 1) (hb : d363696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363120, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363120, d363696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100287 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d360726 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363121 q = 1) (hb : d363697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363121, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363121, d363697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363122 q = 1) (hb : d363698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363122, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d363122, d363698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d363123 q = 1) (hb : d363699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363123, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d363123, d363699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d363124 q = 1) (hb : d363700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363124, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d363124, d363700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d363125 q = 1) (hb : d363701 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d363125, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d363125, d363701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100289 (p : Pattern) (ha : d363131 p = 1) (hb : d363707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363126 q = 1) (hb : d363702 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d363126, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363126, d363702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100288 q ha hb
  have h2 (q : Pattern) (ha : d363127 q = 1) (hb : d363703 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d363127, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363127, d363703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d363128 q = 1) (hb : d363704 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d363128, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363128, d363704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d363129 q = 1) (hb : d363705 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d363129, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363129, d363705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363130 q = 1) (hb : d363706 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d363130, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363130, d363706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363131 q = 1) (hb : d363707 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d363131, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363131, d363707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100290 (p : Pattern) (ha : d363713 p = 1) (hb : d363757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d363092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363132 q = 1) (hb : d363708 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d363132, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363132, d363708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100289 q ha hb
  have h4 (q : Pattern) (ha : d363133 q = 1) (hb : d363709 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d363133, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363133, d363709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363134 q = 1) (hb : d363710 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d363134, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363134, d363710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363134 q = 1) (hb : d363711 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363712 q = 1) (hb : d363756 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363712, d363756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d363712, d363756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d363713 q = 1) (hb : d363757 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363713, d363757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363713, d363757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h8 p ha hb
theorem andIntro100291 (p : Pattern) (ha : d363719 p = 1) (hb : d363763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363714 q = 1) (hb : d363758 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363714, d363758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100290 q ha hb
    | true =>
      simp only [d363714, d363758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363715 q = 1) (hb : d363759 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363715, d363759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363715, d363759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363716 q = 1) (hb : d363760 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363716, d363760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363716, d363760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363717 q = 1) (hb : d363761 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363717, d363761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363717, d363761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363718 q = 1) (hb : d363762 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363718, d363762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363718, d363762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363719 q = 1) (hb : d363763 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363719, d363763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363719, d363763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100292 (p : Pattern) (ha : d363725 p = 1) (hb : d363769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363720 q = 1) (hb : d363764 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363720, d363764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100291 q ha hb
    | true =>
      simp only [d363720, d363764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363721 q = 1) (hb : d363765 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363721, d363765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363721, d363765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363722 q = 1) (hb : d363766 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363722, d363766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363722, d363766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363723 q = 1) (hb : d363767 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363723, d363767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363723, d363767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363724 q = 1) (hb : d363768 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363724, d363768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363724, d363768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363725 q = 1) (hb : d363769 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363725, d363769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363725, d363769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100293 (p : Pattern) (ha : d363731 p = 1) (hb : d363775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363726 q = 1) (hb : d363770 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363726, d363770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100292 q ha hb
    | true =>
      simp only [d363726, d363770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363727 q = 1) (hb : d363771 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363727, d363771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363727, d363771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363728 q = 1) (hb : d363772 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363728, d363772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363728, d363772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363729 q = 1) (hb : d363773 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363729, d363773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363729, d363773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363730 q = 1) (hb : d363774 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363730, d363774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363730, d363774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363731 q = 1) (hb : d363775 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363731, d363775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363731, d363775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100294 (p : Pattern) (ha : d363737 p = 1) (hb : d363781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363732 q = 1) (hb : d363776 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363732, d363776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100293 q ha hb
    | true =>
      simp only [d363732, d363776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363733 q = 1) (hb : d363777 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363733, d363777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363733, d363777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363734 q = 1) (hb : d363778 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363734, d363778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363734, d363778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363735 q = 1) (hb : d363779 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363735, d363779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363735, d363779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363736 q = 1) (hb : d363780 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363736, d363780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363736, d363780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363737 q = 1) (hb : d363781 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363737, d363781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363737, d363781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100295 (p : Pattern) (ha : d363743 p = 1) (hb : d363787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363738 q = 1) (hb : d363782 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363738, d363782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100294 q ha hb
    | true =>
      simp only [d363738, d363782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363739 q = 1) (hb : d363783 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363739, d363783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363739, d363783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363740 q = 1) (hb : d363784 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363740, d363784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363740, d363784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363741 q = 1) (hb : d363785 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363741, d363785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363741, d363785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363742 q = 1) (hb : d363786 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363742, d363786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363742, d363786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363743 q = 1) (hb : d363787 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363743, d363787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363743, d363787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100296 (p : Pattern) (ha : d363749 p = 1) (hb : d363793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363744 q = 1) (hb : d363788 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363744, d363788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100295 q ha hb
    | true =>
      simp only [d363744, d363788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363745 q = 1) (hb : d363789 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363745, d363789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363745, d363789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363746 q = 1) (hb : d363790 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363746, d363790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363746, d363790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363747 q = 1) (hb : d363791 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363747, d363791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363747, d363791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363748 q = 1) (hb : d363792 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363748, d363792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363748, d363792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363749 q = 1) (hb : d363793 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363749, d363793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363749, d363793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100297 (p : Pattern) (ha : d363755 p = 1) (hb : d363799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363750 q = 1) (hb : d363794 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363750, d363794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100296 q ha hb
    | true =>
      simp only [d363750, d363794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d363751 q = 1) (hb : d363795 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363751, d363795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363751, d363795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d363752 q = 1) (hb : d363796 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363752, d363796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363752, d363796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d363753 q = 1) (hb : d363797 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363753, d363797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363753, d363797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d363754 q = 1) (hb : d363798 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363754, d363798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363754, d363798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d363755 q = 1) (hb : d363799 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363755, d363799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363755, d363799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100298 (p : Pattern) (ha : d308 p = 1) (hb : d1087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1086 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1087 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100299 (p : Pattern) (ha : d308 p = 1) (hb : d1093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1086 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100300 (p : Pattern) (ha : d308 p = 1) (hb : d42249 p = 1) : d1563 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42247 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42248 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42248, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42249 q = 1) : d1563 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42249, d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42249, d1563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro100301 (p : Pattern) (ha : d308 p = 1) (hb : d42363 p = 1) : d43856 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1523 q = 1) : d1523 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42361 q = 1) : d42592 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42247 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42362 q = 1) : d43851 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42362, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42362, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42248 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42248, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42363 q = 1) : d43856 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42363, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42363, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro100302 (p : Pattern) (ha : d308 p = 1) (hb : d42594 p = 1) : d43852 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42591 q = 1) : d42591 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42592 q = 1) : d42592 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
    exact ha
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
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42247 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42247, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42593 q = 1) : d43851 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42593, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42593, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42594 q = 1) : d43852 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42594, d43852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42594, d43852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro100303 (p : Pattern) (ha : d308 p = 1) (hb : d42941 p = 1) : d43867 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d2002 q = 1) : d2002 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d2005 q = 1) : d2005 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
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
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42940 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42940, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42940, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42941 q = 1) : d43867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42941, d43867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42941, d43867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100304 (p : Pattern) (ha : d308 p = 1) (hb : d42945 p = 1) : d43856 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42592 q = 1) : d42592 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42598 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42944 q = 1) : d43851 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42944, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42944, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42600 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42600, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42945 q = 1) : d43856 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42945, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42945, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100305 (p : Pattern) (ha : d308 p = 1) (hb : d43288 p = 1) : d363918 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42938 q = 1) : d42938 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43280 q = 1) : d363912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42942 q = 1) : d43868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100303 q ha hb
    | true =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42943 q = 1) : d43869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42946 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100304 q ha hb
    | true =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42947 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42948 q = 1) : d43870 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43281 q = 1) : d363913 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43281, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43281, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43282 q = 1) : d363914 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43282, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43282, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43283 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100299 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43284 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43285 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42951 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42951, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43286 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43286, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43286, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43287 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43287, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43287, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43288 q = 1) : d363918 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43288, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43288, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro100306 (p : Pattern) (ha : d308 p = 1) (hb : d42601 p = 1) : d43856 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1523 q = 1) : d1523 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42361 q = 1) : d42592 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42598 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42599 q = 1) : d43851 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42599, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42599, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h12 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42600 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42600, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42601 q = 1) : d43856 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42601, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42601, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro100307 (p : Pattern) (ha : d308 p = 1) (hb : d42961 p = 1) : d43856 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d1523 q = 1) : d1523 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d308 q = 1) : d308 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42246 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42246, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42361 q = 1) : d42592 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42361, d42592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1519 q = 1) : d1519 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d1540 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42959 q = 1) : d43851 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42959, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42959, d43851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42960 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42960, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42960, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42961 q = 1) : d43856 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42961, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42961, d43856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100308 (p : Pattern) (ha : d308 p = 1) (hb : d43300 p = 1) : d363925 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43283 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100299 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43284 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43285 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42602 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100306 q ha hb
    | true =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42603 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42604 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43293 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43293, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43294 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43294, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43295 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43296 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43297 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43298 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43299 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43300 q = 1) : d363925 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43300, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43300, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100309 (p : Pattern) (ha : d308 p = 1) (hb : d43309 p = 1) : d363933 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42962 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42963 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43306 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43306, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43306, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43307 q = 1) : d363931 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43307, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43307, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43308 q = 1) : d363932 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43308, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43308, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43295 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43296 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43297 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43298 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43299 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43309 q = 1) : d363933 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43309, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43309, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100310 (p : Pattern) (ha : d308 p = 1) (hb : d43318 p = 1) : d363940 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43283 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100299 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43284 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43314 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43314, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43314, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43315 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43315, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43315, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43316 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43316, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43316, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43317 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43317, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43317, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d1116 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d1117 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d1118 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43318 q = 1) : d363940 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43318, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43318, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro100311 (p : Pattern) (ha : d308 p = 1) (hb : d43324 p = 1) : d363946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43289 q = 1) : d363919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43289, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100305 q ha hb
    | true =>
      simp only [d43289, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43290 q = 1) : d363920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43290, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43290, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43291 q = 1) : d363921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43291, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43291, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43292 q = 1) : d363922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43292, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43292, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43301 q = 1) : d363926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43301, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100308 q ha hb
    | true =>
      simp only [d43301, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43302 q = 1) : d363927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43302, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43302, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43303 q = 1) : d363928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43303, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43303, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43304 q = 1) : d363929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43304, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43304, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43305 q = 1) : d363930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43305, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43305, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43310 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
    | true =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43311 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43312 q = 1) : d363936 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43312, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43312, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43313 q = 1) : d363937 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43313, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43313, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43321 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43322 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43323 q = 1) : d363945 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43323, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43323, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43324 q = 1) : d363946 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43324, d363946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43324, d363946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100312 (p : Pattern) (ha : d308 p = 1) (hb : d43330 p = 1) : d363947 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43283 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100299 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43284 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43285 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43285, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42602 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100306 q ha hb
    | true =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42603 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42604 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43293 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43293, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43294 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43294, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43325 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d43325, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43326 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43326, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43327 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43327, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43328 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43328, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43329 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43329, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43330 q = 1) : d363947 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43330, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43330, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100313 (p : Pattern) (ha : d308 p = 1) (hb : d43335 p = 1) : d363940 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43283 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d43283, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100299 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43284 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43284, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43325 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d43325, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43326 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43326, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43327 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43327, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43328 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43328, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43329 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43329, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d1116 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d1117 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h16 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d1118 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43335 q = 1) : d363940 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43335, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43335, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100314 (p : Pattern) (ha : d308 p = 1) (hb : d43342 p = 1) : d363954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43331 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100312 q ha hb
    | true =>
      simp only [d43331, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43332 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43332, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43333 q = 1) : d363950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43333, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43333, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43334 q = 1) : d363951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43334, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43334, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43338 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43339 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43340 q = 1) : d363952 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43340, d363952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43340, d363952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43321 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43322 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43341 q = 1) : d363953 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43341, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43341, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43342 q = 1) : d363954 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43342, d363954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43342, d363954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100315 (p : Pattern) (ha : d308 p = 1) (hb : d9843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d1116 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d1132 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d9841 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d9842 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro100316 (p : Pattern) (ha : d308 p = 1) (hb : d43347 p = 1) : d363958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43338 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43339 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43346 q = 1) : d363953 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43346, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43346, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100315 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d14770 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d14771 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43347 q = 1) : d363958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43347, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43347, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100317 (p : Pattern) (ha : d308 p = 1) (hb : d43354 p = 1) : d363965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43343 q = 1) : d363955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100311 q ha hb
    | true =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43344 q = 1) : d363956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43345 q = 1) : d363957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43348 q = 1) : d363959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
    | true =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100316 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43349 q = 1) : d363960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43350 q = 1) : d363961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43351 q = 1) : d363962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43352 q = 1) : d363963 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43352, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43353 q = 1) : d363964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43353, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43353, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43354 q = 1) : d363965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43354, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43354, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100318 (p : Pattern) (ha : d308 p = 1) (hb : d43358 p = 1) : d363969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43348 q = 1) : d363959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
    | true =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100316 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43349 q = 1) : d363960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43350 q = 1) : d363961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43352 q = 1) : d363963 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43352, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43357 q = 1) : d363968 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43357, d363968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43357, d363968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43358 q = 1) : d363969 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43358, d363969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43358, d363969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100319 (p : Pattern) (ha : d308 p = 1) (hb : d43364 p = 1) : d363975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43362 q = 1) : d363973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43363 q = 1) : d363974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43364 q = 1) : d363975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43364, d363975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43364, d363975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100320 (p : Pattern) (ha : d308 p = 1) (hb : d43368 p = 1) : d363979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43366 q = 1) : d363977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43367 q = 1) : d363978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43368 q = 1) : d363979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43368, d363979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43368, d363979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100321 (p : Pattern) (ha : d308 p = 1) (hb : d43374 p = 1) : d363985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43369 q = 1) : d363980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100319 q ha hb
    | true =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100320 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43370 q = 1) : d363981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43371 q = 1) : d363982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43372 q = 1) : d363983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43373 q = 1) : d363984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43374 q = 1) : d363985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43374, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43374, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100322 (p : Pattern) (ha : d308 p = 1) (hb : d43377 p = 1) : d363988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43362 q = 1) : d363973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43363 q = 1) : d363974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43377 q = 1) : d363988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43377, d363988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43377, d363988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100323 (p : Pattern) (ha : d308 p = 1) (hb : d43378 p = 1) : d363989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43366 q = 1) : d363977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43367 q = 1) : d363978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43378 q = 1) : d363989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43378, d363989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43378, d363989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100324 (p : Pattern) (ha : d308 p = 1) (hb : d43384 p = 1) : d363995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43369 q = 1) : d363980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100319 q ha hb
    | true =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100320 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43370 q = 1) : d363981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43371 q = 1) : d363982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43372 q = 1) : d363983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43373 q = 1) : d363984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43379 q = 1) : d363990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100322 q ha hb
    | true =>
      simp only [d43379, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100323 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43380 q = 1) : d363991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43380, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43381 q = 1) : d363992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43381, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43382 q = 1) : d363993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43382, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43383 q = 1) : d363994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43383, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43384 q = 1) : d363995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43384, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43384, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100325 (p : Pattern) (ha : d308 p = 1) (hb : d43630 p = 1) : d364096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43369 q = 1) : d363980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100319 q ha hb
    | true =>
      simp only [d43369, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100320 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43370 q = 1) : d363981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43370, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43371 q = 1) : d363982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43372 q = 1) : d363983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43372, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43373 q = 1) : d363984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43373, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43625 q = 1) : d364091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100320 q ha hb
    | true =>
      simp only [d43625, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43626 q = 1) : d364092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43626, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43627 q = 1) : d364093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43627, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43628 q = 1) : d364094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43628, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43629 q = 1) : d364095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43629, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43630 q = 1) : d364096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43630, d364096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43630, d364096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100326 (p : Pattern) (ha : d308 p = 1) (hb : d43636 p = 1) : d364102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43625 q = 1) : d364091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100320 q ha hb
    | true =>
      simp only [d43625, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43626 q = 1) : d364092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43626, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43627 q = 1) : d364093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43627, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43628 q = 1) : d364094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43628, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43629 q = 1) : d364095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43629, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43631 q = 1) : d364097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100323 q ha hb
    | true =>
      simp only [d43631, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43632 q = 1) : d364098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43632, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43633 q = 1) : d364099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43633, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43634 q = 1) : d364100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43634, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43635 q = 1) : d364101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43635, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43636 q = 1) : d364102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43636, d364102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43636, d364102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100327 (p : Pattern) (ha : d308 p = 1) (hb : d43645 p = 1) : d364111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43631 q = 1) : d364097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100323 q ha hb
    | true =>
      simp only [d43631, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43632 q = 1) : d364098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43632, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43633 q = 1) : d364099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43633, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43634 q = 1) : d364100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43634, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43635 q = 1) : d364101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43635, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43645 q = 1) : d364111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43645, d364111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43645, d364111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100328 (p : Pattern) (ha : d308 p = 1) (hb : d43708 p = 1) : d364165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43699 q = 1) : d364160 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43699, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43699, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100312 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43331 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100312 q ha hb
    | true =>
      simp only [d43331, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43700 q = 1) : d364161 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43700, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43700, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43332 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43332, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43701 q = 1) : d364162 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43701, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43701, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43702 q = 1) : d364163 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43702, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43702, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43703 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43704 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43705 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43706 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43707 q = 1) : d364164 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43707, d364164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43707, d364164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43679 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43680 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43681 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43682 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43693 q = 1) : d364154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43693, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43693, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43708 q = 1) : d364165 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43708, d364165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43708, d364165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100329 (p : Pattern) (ha : d308 p = 1) (hb : d43713 p = 1) : d364169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43703 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43704 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43705 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43706 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43712 q = 1) : d364154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43712, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43712, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d15019 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100315 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100315 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d15020 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d15021 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d15022 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43713 q = 1) : d364169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43713, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43713, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100330 (p : Pattern) (ha : d308 p = 1) (hb : d43732 p = 1) : d364188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43714 q = 1) : d364170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
    | true =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100329 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43715 q = 1) : d364171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43716 q = 1) : d364172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43722 q = 1) : d364178 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43722, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43722, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43731 q = 1) : d364187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43731, d364187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43731, d364187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43732 q = 1) : d364188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43732, d364188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43732, d364188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100331 (p : Pattern) (ha : d308 p = 1) (hb : d43821 p = 1) : d364211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43733 q = 1) : d364189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43733, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100330 q ha hb
    | true =>
      simp only [d43733, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43734 q = 1) : d364190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43734, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43734, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43818 q = 1) : d364208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43818, d364208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43818, d364208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43819 q = 1) : d364209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43819, d364209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43819, d364209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43820 q = 1) : d364210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43820, d364210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43820, d364210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43821 q = 1) : d364211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43821, d364211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43821, d364211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100332 (p : Pattern) (ha : d308 p = 1) (hb : d43827 p = 1) : d364217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43822 q = 1) : d364212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43822, d364212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100331 q ha hb
    | true =>
      simp only [d43822, d364212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43823 q = 1) : d364213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43823, d364213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43823, d364213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43824 q = 1) : d364214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43824, d364214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43824, d364214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43825 q = 1) : d364215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43825, d364215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43825, d364215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43826 q = 1) : d364216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43826, d364216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43826, d364216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43827 q = 1) : d364217 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43827, d364217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43827, d364217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100333 (p : Pattern) (ha : d308 p = 1) (hb : d43389 p = 1) : d364000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43362 q = 1) : d363973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43388 q = 1) : d363999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43388, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43388, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43389 q = 1) : d364000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43389, d364000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43389, d364000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100334 (p : Pattern) (ha : d308 p = 1) (hb : d43391 p = 1) : d364002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43366 q = 1) : d363977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43390 q = 1) : d364001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43390, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43390, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43391 q = 1) : d364002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43391, d364002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43391, d364002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100335 (p : Pattern) (ha : d308 p = 1) (hb : d43398 p = 1) : d364009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43396 q = 1) : d364007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43396, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43396, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43397 q = 1) : d364008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43397, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43397, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43398 q = 1) : d364009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43398, d364009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43398, d364009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100336 (p : Pattern) (ha : d308 p = 1) (hb : d43401 p = 1) : d364012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43399 q = 1) : d364010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43399, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43399, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43400 q = 1) : d364011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43400, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43400, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43401 q = 1) : d364012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43401, d364012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43401, d364012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100337 (p : Pattern) (ha : d308 p = 1) (hb : d43406 p = 1) : d2007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d2005 q = 1) : d2005 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42940 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42940, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42940, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43406 q = 1) : d2007 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43406, d2007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43406, d2007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100338 (p : Pattern) (ha : d308 p = 1) (hb : d43415 p = 1) : d364020 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43405 q = 1) : d43405 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43407 q = 1) : d43846 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43407, d43846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100337 q ha hb
    | true =>
      simp only [d43407, d43846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43408 q = 1) : d43847 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43408, d43847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43408, d43847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43409 q = 1) : d43848 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43409, d43848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d43409, d43848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43410 q = 1) : d364016 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43410, d364016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43410, d364016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43411 q = 1) : d364017 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43411, d364017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43411, d364017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42938 q = 1) : d42938 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43280 q = 1) : d363912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42946 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100304 q ha hb
    | true =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42947 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43412 q = 1) : d43859 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43412, d43859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43412, d43859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43413 q = 1) : d364018 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43413, d364018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43413, d364018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43414 q = 1) : d364019 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43414, d364019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43414, d364019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43415 q = 1) : d364020 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43415, d364020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43415, d364020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100339 (p : Pattern) (ha : d308 p = 1) (hb : d43421 p = 1) : d43874 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42591 q = 1) : d42591 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d34366 q = 1) : d34366 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d1519 q = 1) : d1519 q = 1 := by
    exact hb
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d1540 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1540, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43420 q = 1) : d43873 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d43420, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43420, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43421 q = 1) : d43874 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43421, d43874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43421, d43874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100340 (p : Pattern) (ha : d308 p = 1) (hb : d43427 p = 1) : d364028 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42938 q = 1) : d42938 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43280 q = 1) : d363912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43280, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42942 q = 1) : d43868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100303 q ha hb
    | true =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42943 q = 1) : d43869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42946 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100304 q ha hb
    | true =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42947 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42948 q = 1) : d43870 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43281 q = 1) : d363913 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43281, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43281, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43282 q = 1) : d363914 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43282, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43282, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43422 q = 1) : d43886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43422, d43886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100339 q ha hb
    | true =>
      simp only [d43422, d43886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43423 q = 1) : d43887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43423, d43887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43423, d43887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42962 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42963 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43424 q = 1) : d364025 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43424, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43424, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43425 q = 1) : d364026 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43425, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43425, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43426 q = 1) : d364027 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43426, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d43426, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43427 q = 1) : d364028 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43427, d364028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43427, d364028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100341 (p : Pattern) (ha : d308 p = 1) (hb : d43436 p = 1) : d364034 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42938 q = 1) : d42938 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43422 q = 1) : d43886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43422, d43886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100339 q ha hb
    | true =>
      simp only [d43422, d43886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43423 q = 1) : d43887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43423, d43887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43423, d43887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43433 q = 1) : d43995 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43433, d43995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43433, d43995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43434 q = 1) : d43996 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43434, d43996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43434, d43996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43435 q = 1) : d43997 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43435, d43997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43435, d43997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42962 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42963 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43424 q = 1) : d364025 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43424, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43424, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43425 q = 1) : d364026 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43425, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43425, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43426 q = 1) : d364027 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43426, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43426, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43436 q = 1) : d364034 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43436, d364034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43436, d364034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro100342 (p : Pattern) (ha : d308 p = 1) (hb : d43442 p = 1) : d364040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43416 q = 1) : d364021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43416, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100338 q ha hb
    | true =>
      simp only [d43416, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43417 q = 1) : d364022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43417, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43417, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43418 q = 1) : d364023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43418, d364023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43418, d364023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43419 q = 1) : d364024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43419, d364024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43419, d364024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43428 q = 1) : d364029 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43428, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100340 q ha hb
    | true =>
      simp only [d43428, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43429 q = 1) : d364030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43429, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43429, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43430 q = 1) : d364031 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43430, d364031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43430, d364031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43431 q = 1) : d364032 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43431, d364032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43431, d364032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43432 q = 1) : d364033 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43432, d364033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43432, d364033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43437 q = 1) : d364035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43437, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100341 q ha hb
    | true =>
      simp only [d43437, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43438 q = 1) : d364036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43438, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43438, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43439 q = 1) : d364037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43439, d364037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43439, d364037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43440 q = 1) : d364038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43440, d364038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43440, d364038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43310 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
    | true =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43311 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43312 q = 1) : d363936 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43312, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43312, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43313 q = 1) : d363937 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43313, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43313, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43441 q = 1) : d364039 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43441, d364039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43441, d364039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43442 q = 1) : d364040 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43442, d364040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43442, d364040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100343 (p : Pattern) (ha : d308 p = 1) (hb : d43449 p = 1) : d363933 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d43278 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d43278, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100298 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43279 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43295 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d43295, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43296 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43296, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43446 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43446, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43446, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43447 q = 1) : d363931 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43447, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43447, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43448 q = 1) : d363932 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43448, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43448, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43297 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43297, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43298 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43298, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43299 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43299, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43449 q = 1) : d363933 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43449, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43449, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100344 (p : Pattern) (ha : d308 p = 1) (hb : d43455 p = 1) : d364044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43450 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43450, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100343 q ha hb
    | true =>
      simp only [d43450, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43451 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43451, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43451, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43452 q = 1) : d363936 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43452, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43452, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43453 q = 1) : d363937 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43453, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43453, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43321 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43321, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43322 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43322, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43454 q = 1) : d363945 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43454, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43454, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43341 q = 1) : d363953 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43341, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43341, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43455 q = 1) : d364044 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43455, d364044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43455, d364044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100345 (p : Pattern) (ha : d308 p = 1) (hb : d43461 p = 1) : d364050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43443 q = 1) : d364041 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43443, d364041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100342 q ha hb
    | true =>
      simp only [d43443, d364041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100311 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43444 q = 1) : d364042 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43444, d364042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43444, d364042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43445 q = 1) : d364043 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43445, d364043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43445, d364043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43456 q = 1) : d364045 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43456, d364045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100311 q ha hb
    | true =>
      simp only [d43456, d364045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100344 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43457 q = 1) : d364046 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43457, d364046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43457, d364046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43458 q = 1) : d364047 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43458, d364047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43458, d364047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43459 q = 1) : d364048 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43459, d364048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43459, d364048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43343 q = 1) : d363955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100311 q ha hb
    | true =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43344 q = 1) : d363956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43345 q = 1) : d363957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43348 q = 1) : d363959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
    | true =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100316 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43349 q = 1) : d363960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43350 q = 1) : d363961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43351 q = 1) : d363962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43460 q = 1) : d364049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43460, d364049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43460, d364049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43461 q = 1) : d364050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43461, d364050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43461, d364050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100346 (p : Pattern) (ha : d308 p = 1) (hb : d43467 p = 1) : d364056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43462 q = 1) : d364051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43462, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100345 q ha hb
    | true =>
      simp only [d43462, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43463 q = 1) : d364052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43463, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43463, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43464 q = 1) : d364053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43464, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43464, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43465 q = 1) : d364054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43465, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43465, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43466 q = 1) : d364055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43466, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43466, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43467 q = 1) : d364056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43467, d364056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43467, d364056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100347 (p : Pattern) (ha : d308 p = 1) (hb : d43581 p = 1) : d363958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43338 q = 1) : d363943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43338, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43339 q = 1) : d363944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43339, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43346 q = 1) : d363953 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43346, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43346, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43581 q = 1) : d363958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43581, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43581, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100348 (p : Pattern) (ha : d308 p = 1) (hb : d43587 p = 1) : d363965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43343 q = 1) : d363955 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100311 q ha hb
    | true =>
      simp only [d43343, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43344 q = 1) : d363956 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43344, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43345 q = 1) : d363957 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43345, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43348 q = 1) : d363959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
    | true =>
      simp only [d43348, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100316 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43349 q = 1) : d363960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43349, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43350 q = 1) : d363961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43350, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43351 q = 1) : d363962 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43351, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43582 q = 1) : d363959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43582, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100314 q ha hb
    | true =>
      simp only [d43582, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100347 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43583 q = 1) : d363960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43583, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43583, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43584 q = 1) : d363961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43584, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43584, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43585 q = 1) : d363963 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43585, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43585, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43586 q = 1) : d363964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43586, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43586, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43587 q = 1) : d363965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43587, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43587, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100349 (p : Pattern) (ha : d308 p = 1) (hb : d43593 p = 1) : d364062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43588 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43588, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100348 q ha hb
    | true =>
      simp only [d43588, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43589 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43589, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43589, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43590 q = 1) : d364059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43590, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43590, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43591 q = 1) : d364060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43591, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43591, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43592 q = 1) : d364061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43592, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43592, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43593 q = 1) : d364062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43593, d364062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43593, d364062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100350 (p : Pattern) (ha : d308 p = 1) (hb : d309929 p = 1) : d364068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43392 q = 1) : d364003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43392, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100333 q ha hb
    | true =>
      simp only [d43392, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100334 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43393 q = 1) : d364004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43393, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43393, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43394 q = 1) : d364005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43394, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43394, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43395 q = 1) : d364006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43395, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43395, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43402 q = 1) : d364013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43402, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100335 q ha hb
    | true =>
      simp only [d43402, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100336 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43403 q = 1) : d364014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43403, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43403, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43404 q = 1) : d364015 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43404, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43404, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43468 q = 1) : d364057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43468, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100346 q ha hb
    | true =>
      simp only [d43468, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100319 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309925 q = 1) : d364058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309925, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43594 q = 1) : d364063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43594, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100349 q ha hb
    | true =>
      simp only [d43594, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43595 q = 1) : d364064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43595, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43595, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309926 q = 1) : d364065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309926, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309927 q = 1) : d364066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309927, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309928 q = 1) : d364067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309928, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309929 q = 1) : d364068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309929, d364068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309929, d364068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100351 (p : Pattern) (ha : d308 p = 1) (hb : d43600 p = 1) : d364069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43362 q = 1) : d363973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43388 q = 1) : d363999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43388, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43388, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43600 q = 1) : d364069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43600, d364069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43600, d364069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100352 (p : Pattern) (ha : d308 p = 1) (hb : d43601 p = 1) : d364070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43366 q = 1) : d363977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43390 q = 1) : d364001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43390, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43390, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43601 q = 1) : d364070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43601, d364070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43601, d364070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100353 (p : Pattern) (ha : d308 p = 1) (hb : d43606 p = 1) : d364075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43361 q = 1) : d363972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43396 q = 1) : d364007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43396, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43396, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43397 q = 1) : d364008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43397, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43397, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43606 q = 1) : d364075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43606, d364075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43606, d364075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100354 (p : Pattern) (ha : d308 p = 1) (hb : d43607 p = 1) : d364076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43359 q = 1) : d363970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100318 q ha hb
    | true =>
      simp only [d43359, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43360 q = 1) : d363971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43360, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43365 q = 1) : d363976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43399 q = 1) : d364010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43399, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43399, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43400 q = 1) : d364011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43400, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43400, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43607 q = 1) : d364076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43607, d364076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43607, d364076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100355 (p : Pattern) (ha : d308 p = 1) (hb : d43611 p = 1) : d364080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43462 q = 1) : d364051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43462, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100345 q ha hb
    | true =>
      simp only [d43462, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43463 q = 1) : d364052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43463, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43463, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43355 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100317 q ha hb
    | true =>
      simp only [d43355, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43356 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43356, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43464 q = 1) : d364053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43464, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43464, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43465 q = 1) : d364054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43465, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43465, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43466 q = 1) : d364055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43466, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43466, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43611 q = 1) : d364080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43611, d364080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43611, d364080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100356 (p : Pattern) (ha : d308 p = 1) (hb : d43617 p = 1) : d364083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43588 q = 1) : d363966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43588, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100348 q ha hb
    | true =>
      simp only [d43588, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43589 q = 1) : d363967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43589, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43589, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43590 q = 1) : d364059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43590, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43590, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43591 q = 1) : d364060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43591, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43591, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43592 q = 1) : d364061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43592, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43592, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43617 q = 1) : d364083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43617, d364083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43617, d364083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100357 (p : Pattern) (ha : d308 p = 1) (hb : d309934 p = 1) : d364089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43392 q = 1) : d364003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43392, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100333 q ha hb
    | true =>
      simp only [d43392, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100334 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43393 q = 1) : d364004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43393, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43393, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43394 q = 1) : d364005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43394, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43394, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43395 q = 1) : d364006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43395, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43395, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43402 q = 1) : d364013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43402, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100335 q ha hb
    | true =>
      simp only [d43402, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100336 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43403 q = 1) : d364014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43403, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43403, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43404 q = 1) : d364015 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43404, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43404, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43468 q = 1) : d364057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43468, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100346 q ha hb
    | true =>
      simp only [d43468, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100319 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309925 q = 1) : d364058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309925, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43594 q = 1) : d364063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43594, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100349 q ha hb
    | true =>
      simp only [d43594, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43595 q = 1) : d364064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43595, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43595, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309926 q = 1) : d364065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309926, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309927 q = 1) : d364066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309927, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309928 q = 1) : d364067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309928, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43602 q = 1) : d364071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43602, d364071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100351 q ha hb
    | true =>
      simp only [d43602, d364071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100352 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43603 q = 1) : d364072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43603, d364072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43603, d364072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43604 q = 1) : d364073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43604, d364073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43604, d364073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43605 q = 1) : d364074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43605, d364074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43605, d364074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43608 q = 1) : d364077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43608, d364077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100353 q ha hb
    | true =>
      simp only [d43608, d364077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100354 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43609 q = 1) : d364078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43609, d364078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43609, d364078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43610 q = 1) : d364079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43610, d364079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43610, d364079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d43612 q = 1) : d364081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43612, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100355 q ha hb
    | true =>
      simp only [d43612, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100322 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309930 q = 1) : d364082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309930, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d43618 q = 1) : d364084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43618, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100356 q ha hb
    | true =>
      simp only [d43618, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d43619 q = 1) : d364085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43619, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43619, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309931 q = 1) : d364086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309931, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309932 q = 1) : d364087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309932, d364087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309932, d364087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309933 q = 1) : d364088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309933, d364088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309933, d364088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309934 q = 1) : d364089 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309934, d364089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309934, d364089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100358 (p : Pattern) (ha : d308 p = 1) (hb : d309941 p = 1) : d364109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43612 q = 1) : d364081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43612, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100355 q ha hb
    | true =>
      simp only [d43612, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100322 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309930 q = 1) : d364082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309930, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43618 q = 1) : d364084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43618, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100356 q ha hb
    | true =>
      simp only [d43618, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43619 q = 1) : d364085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43619, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43619, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309931 q = 1) : d364086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309931, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309939 q = 1) : d364107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309939, d364107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309939, d364107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309940 q = 1) : d364108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309940, d364108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309940, d364108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309941 q = 1) : d364109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309941, d364109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309941, d364109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100359 (p : Pattern) (ha : d308 p = 1) (hb : d43669 p = 1) : d364135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43651 q = 1) : d364117 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43651, d364117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43651, d364117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100338 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43416 q = 1) : d364021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43416, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100338 q ha hb
    | true =>
      simp only [d43416, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43652 q = 1) : d364118 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43652, d364118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43652, d364118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43417 q = 1) : d364022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43417, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43417, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43653 q = 1) : d364119 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43653, d364119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43653, d364119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43654 q = 1) : d364120 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43654, d364120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43654, d364120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43655 q = 1) : d364121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43655, d364121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43655, d364121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100340 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43428 q = 1) : d364029 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43428, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100340 q ha hb
    | true =>
      simp only [d43428, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43656 q = 1) : d364122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43656, d364122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43656, d364122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43429 q = 1) : d364030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43429, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43429, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43657 q = 1) : d364123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43657, d364123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43657, d364123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43658 q = 1) : d364124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43658, d364124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43658, d364124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43659 q = 1) : d364125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43659, d364125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43659, d364125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43660 q = 1) : d364126 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43660, d364126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43660, d364126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100341 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43437 q = 1) : d364035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43437, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100341 q ha hb
    | true =>
      simp only [d43437, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43661 q = 1) : d364127 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43661, d364127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43661, d364127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43438 q = 1) : d364036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43438, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43438, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43662 q = 1) : d364128 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43662, d364128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43662, d364128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43663 q = 1) : d364129 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43663, d364129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43663, d364129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43664 q = 1) : d364130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43664, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43664, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43310 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
    | true =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d43665 q = 1) : d364131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43665, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43665, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d43311 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d43666 q = 1) : d364132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43666, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d43666, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d43667 q = 1) : d364133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43667, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43667, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d43668 q = 1) : d364134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43668, d364134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43668, d364134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d43669 q = 1) : d364135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43669, d364135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43669, d364135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100360 (p : Pattern) (ha : d308 p = 1) (hb : d43684 p = 1) : d364150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43670 q = 1) : d364136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43670, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43670, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100305 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43289 q = 1) : d363919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43289, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100305 q ha hb
    | true =>
      simp only [d43289, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43671 q = 1) : d364137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43671, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43671, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43290 q = 1) : d363920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43290, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43290, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43672 q = 1) : d364138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43672, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43672, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43673 q = 1) : d364139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43673, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43673, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43674 q = 1) : d364140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43674, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43674, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100308 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43301 q = 1) : d363926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43301, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100308 q ha hb
    | true =>
      simp only [d43301, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43675 q = 1) : d364141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43675, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43675, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43302 q = 1) : d363927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43302, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43302, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43676 q = 1) : d364142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43676, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43676, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43677 q = 1) : d364143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43677, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43677, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43678 q = 1) : d364144 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43678, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43678, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43664 q = 1) : d364130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43664, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43664, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43310 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100309 q ha hb
    | true =>
      simp only [d43310, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43665 q = 1) : d364131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43665, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43665, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43311 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43311, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43666 q = 1) : d364132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43666, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43666, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43667 q = 1) : d364133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43667, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43667, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43679 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d43680 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d43681 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d43682 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d43683 q = 1) : d364149 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43683, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43683, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d43684 q = 1) : d364150 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43684, d364150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43684, d364150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100361 (p : Pattern) (ha : d308 p = 1) (hb : d43694 p = 1) : d364155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43688 q = 1) : d364130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43688, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43688, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100343 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43450 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43450, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100343 q ha hb
    | true =>
      simp only [d43450, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43689 q = 1) : d364131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43689, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43689, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43451 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43451, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43451, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43690 q = 1) : d364132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43690, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43690, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43691 q = 1) : d364133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43691, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43691, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43679 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43679, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43319 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100310 q ha hb
    | true =>
      simp only [d43319, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43680 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43680, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43320 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43320, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43681 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43681, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43682 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43682, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43692 q = 1) : d364149 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43692, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43692, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43693 q = 1) : d364154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43693, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43693, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43694 q = 1) : d364155 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43694, d364155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43694, d364155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100362 (p : Pattern) (ha : d308 p = 1) (hb : d43719 p = 1) : d364175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43685 q = 1) : d364151 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43685, d364151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100359 q ha hb
    | true =>
      simp only [d43685, d364151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100360 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43686 q = 1) : d364152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43686, d364152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43686, d364152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43687 q = 1) : d364153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43687, d364153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43687, d364153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43695 q = 1) : d364156 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43695, d364156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100360 q ha hb
    | true =>
      simp only [d43695, d364156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100361 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43696 q = 1) : d364157 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43696, d364157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43696, d364157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43697 q = 1) : d364158 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43697, d364158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43697, d364158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43698 q = 1) : d364159 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43698, d364159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43698, d364159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43709 q = 1) : d364166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100360 q ha hb
    | true =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43710 q = 1) : d364167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43711 q = 1) : d364168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43714 q = 1) : d364170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
    | true =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100329 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43715 q = 1) : d364171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43716 q = 1) : d364172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43717 q = 1) : d364173 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43718 q = 1) : d364174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43718, d364174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43718, d364174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43719 q = 1) : d364175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43719, d364175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43719, d364175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100363 (p : Pattern) (ha : d308 p = 1) (hb : d43724 p = 1) : d364180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43709 q = 1) : d364166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100360 q ha hb
    | true =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43710 q = 1) : d364167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43711 q = 1) : d364168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43714 q = 1) : d364170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
    | true =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100329 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43715 q = 1) : d364171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43716 q = 1) : d364172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43717 q = 1) : d364173 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43722 q = 1) : d364178 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43722, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43722, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43723 q = 1) : d364179 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43723, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43723, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43724 q = 1) : d364180 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43724, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43724, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100364 (p : Pattern) (ha : d308 p = 1) (hb : d43730 p = 1) : d364186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43720 q = 1) : d364176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43720, d364176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100362 q ha hb
    | true =>
      simp only [d43720, d364176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43721 q = 1) : d364177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43721, d364177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43721, d364177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43725 q = 1) : d364181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43725, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100363 q ha hb
    | true =>
      simp only [d43725, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43726 q = 1) : d364182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43726, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43726, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43727 q = 1) : d364183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43727, d364183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43727, d364183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43728 q = 1) : d364184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43728, d364184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43728, d364184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43729 q = 1) : d364185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43729, d364185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43729, d364185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43730 q = 1) : d364186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43730, d364186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43730, d364186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100365 (p : Pattern) (ha : d308 p = 1) (hb : d43738 p = 1) : d364194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43725 q = 1) : d364181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43725, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100363 q ha hb
    | true =>
      simp only [d43725, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43726 q = 1) : d364182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43726, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43726, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43733 q = 1) : d364189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43733, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100330 q ha hb
    | true =>
      simp only [d43733, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43734 q = 1) : d364190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43734, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43734, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43735 q = 1) : d364191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43735, d364191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43735, d364191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43736 q = 1) : d364192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43736, d364192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43736, d364192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43737 q = 1) : d364193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43737, d364193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43737, d364193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43738 q = 1) : d364194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43738, d364194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43738, d364194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100366 (p : Pattern) (ha : d308 p = 1) (hb : d43798 p = 1) : d364169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43703 q = 1) : d364145 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43703, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43336 q = 1) : d363941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100313 q ha hb
    | true =>
      simp only [d43336, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43704 q = 1) : d364146 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43704, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43337 q = 1) : d363942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43337, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43705 q = 1) : d364147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43705, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43706 q = 1) : d364148 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43706, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43712 q = 1) : d364154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43712, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43712, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43798 q = 1) : d364169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43798, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43798, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100367 (p : Pattern) (ha : d308 p = 1) (hb : d43804 p = 1) : d364180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43709 q = 1) : d364166 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100360 q ha hb
    | true =>
      simp only [d43709, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43710 q = 1) : d364167 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43710, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43711 q = 1) : d364168 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43711, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43714 q = 1) : d364170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
    | true =>
      simp only [d43714, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100329 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43715 q = 1) : d364171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43715, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43716 q = 1) : d364172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43716, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43717 q = 1) : d364173 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43717, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43799 q = 1) : d364170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43799, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100328 q ha hb
    | true =>
      simp only [d43799, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100366 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43800 q = 1) : d364171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43800, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43800, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43801 q = 1) : d364172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43801, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43801, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43802 q = 1) : d364178 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43802, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43802, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43803 q = 1) : d364179 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43803, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43803, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43804 q = 1) : d364180 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43804, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43804, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100368 (p : Pattern) (ha : d308 p = 1) (hb : d43810 p = 1) : d364200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43805 q = 1) : d364181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43805, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100367 q ha hb
    | true =>
      simp only [d43805, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43806 q = 1) : d364182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43806, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43806, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43807 q = 1) : d364197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43807, d364197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43807, d364197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43808 q = 1) : d364198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43808, d364198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43808, d364198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43809 q = 1) : d364199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43809, d364199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43809, d364199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43810 q = 1) : d364200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43810, d364200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43810, d364200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100369 (p : Pattern) (ha : d308 p = 1) (hb : d309951 p = 1) : d364206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43739 q = 1) : d364195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43739, d364195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100364 q ha hb
    | true =>
      simp only [d43739, d364195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100365 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309947 q = 1) : d364196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309947, d364196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309947, d364196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43811 q = 1) : d364201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43811, d364201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100368 q ha hb
    | true =>
      simp only [d43811, d364201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43812 q = 1) : d364202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43812, d364202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43812, d364202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309948 q = 1) : d364203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309948, d364203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309948, d364203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309949 q = 1) : d364204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309949, d364204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309949, d364204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309950 q = 1) : d364205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309950, d364205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309950, d364205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309951 q = 1) : d364206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309951, d364206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309951, d364206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100370 (p : Pattern) (ha : d308 p = 1) (hb : d309957 p = 1) : d364223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43375 q = 1) : d363986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43375, d363986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43375, d363986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100321 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43376 q = 1) : d363987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43376, d363987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43376, d363987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43385 q = 1) : d363996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43385, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100321 q ha hb
    | true =>
      simp only [d43385, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100324 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43386 q = 1) : d363997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43386, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43386, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43387 q = 1) : d363998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d43387, d363998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43387, d363998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309935 q = 1) : d364090 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309935, d364090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100350 q ha hb
    | true =>
      simp only [d309935, d364090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100357 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43637 q = 1) : d364103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43637, d364103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100325 q ha hb
    | true =>
      simp only [d43637, d364103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100326 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309936 q = 1) : d364104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309936, d364104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309936, d364104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309937 q = 1) : d364105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309937, d364105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309937, d364105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309938 q = 1) : d364106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309938, d364106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309938, d364106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309942 q = 1) : d364110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309942, d364110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309942, d364110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100358 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43646 q = 1) : d364112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43646, d364112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43646, d364112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100327 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309943 q = 1) : d364113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309943, d364113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309943, d364113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309944 q = 1) : d364114 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309944, d364114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309944, d364114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309945 q = 1) : d364115 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309945, d364115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309945, d364115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309946 q = 1) : d364116 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309946, d364116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309946, d364116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309952 q = 1) : d364207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309952, d364207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309952, d364207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100369 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43828 q = 1) : d364218 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43828, d364218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43828, d364218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100332 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309953 q = 1) : d364219 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309953, d364219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309953, d364219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309954 q = 1) : d364220 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309954, d364220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309954, d364220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309955 q = 1) : d364221 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309955, d364221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309955, d364221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d309956 q = 1) : d364222 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309956, d364222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309956, d364222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309957 q = 1) : d364223 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309957, d364223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309957, d364223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100371 (p : Pattern) (ha : d308 p = 1) (hb : d309963 p = 1) : d364229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d309958 q = 1) : d364224 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309958, d364224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309958, d364224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100370 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309959 q = 1) : d364225 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309959, d364225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309959, d364225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309960 q = 1) : d364226 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309960, d364226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309960, d364226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d309961 q = 1) : d364227 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309961, d364227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309961, d364227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309962 q = 1) : d364228 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309962, d364228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309962, d364228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309963 q = 1) : d364229 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309963, d364229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309963, d364229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100372 (p : Pattern) (ha : d310011 p = 1) (hb : d363815 p = 1) : d364235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309964 q = 1) : d364230 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309964, d364230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309964, d364230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100371 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309965 q = 1) : d364231 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309965, d364231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309965, d364231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309966 q = 1) (hb : d363813 q = 1) : d364232 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d363813, d364232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309966, d363813, d364232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d310009 q = 1) (hb : d363814 q = 1) : d364233 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d363814, d364233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310009, d363814, d364233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d310010 q = 1) (hb : d363815 q = 1) : d364234 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d363815, d364234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310010, d363815, d364234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d310011 q = 1) (hb : d363815 q = 1) : d364235 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d364235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d310011, d364235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100373 (p : Pattern) (ha : d310017 p = 1) (hb : d363815 p = 1) : d364241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d363815 q = 1) : d364236 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d364236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100372 q ha hb
    | true =>
      simp only [d310012, d364236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d363815 q = 1) : d364237 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d364237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d364237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d363815 q = 1) : d364238 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d364238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d364238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d363815 q = 1) : d364239 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d364239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d364239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d363815 q = 1) : d364240 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d364240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d364240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d363815 q = 1) : d364241 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d364241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d364241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100374 (p : Pattern) (ha : d310023 p = 1) (hb : d363819 p = 1) : d364247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d363815 q = 1) : d364242 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d364242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100373 q ha hb
    | true =>
      simp only [d310018, d364242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d310019 q = 1) (hb : d363816 q = 1) : d364243 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d363816, d364243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d363816, d364243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310020 q = 1) (hb : d363817 q = 1) : d364244 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d363817, d364244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310020, d363817, d364244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d310021 q = 1) (hb : d363818 q = 1) : d364245 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d363818, d364245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310021, d363818, d364245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d310022 q = 1) (hb : d363819 q = 1) : d364246 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d363819, d364246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310022, d363819, d364246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d310023 q = 1) (hb : d363819 q = 1) : d364247 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d364247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310023, d364247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100375 (p : Pattern) (ha : d310029 p = 1) (hb : d363819 p = 1) : d364253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d363819 q = 1) : d364248 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d364248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100374 q ha hb
    | true =>
      simp only [d310024, d364248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d363819 q = 1) : d364249 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d364249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d364249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d363819 q = 1) : d364250 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d364250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d364250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d363819 q = 1) : d364251 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d364251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d364251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d363819 q = 1) : d364252 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d364252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d364252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d363819 q = 1) : d364253 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d364253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d364253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100376 (p : Pattern) (ha : d310035 p = 1) (hb : d363819 p = 1) : d364259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d363819 q = 1) : d364254 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d364254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100375 q ha hb
    | true =>
      simp only [d310030, d364254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d363819 q = 1) : d364255 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d364255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d364255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d363819 q = 1) : d364256 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d364256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d364256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d363819 q = 1) : d364257 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d364257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d364257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d363819 q = 1) : d364258 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d364258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d364258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d363819 q = 1) : d364259 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d364259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d364259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100377 (p : Pattern) (ha : d310041 p = 1) (hb : d363819 p = 1) : d364265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d363819 q = 1) : d364260 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d364260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100376 q ha hb
    | true =>
      simp only [d310036, d364260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d363819 q = 1) : d364261 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d364261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d364261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d363819 q = 1) : d364262 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d364262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d364262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d363819 q = 1) : d364263 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d364263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d364263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d363819 q = 1) : d364264 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d364264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d364264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d363819 q = 1) : d364265 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d364265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d364265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100378 (p : Pattern) (ha : d310047 p = 1) (hb : d363819 p = 1) : d364271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d363819 q = 1) : d364266 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d364266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100377 q ha hb
    | true =>
      simp only [d310042, d364266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d363819 q = 1) : d364267 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d364267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d364267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d363819 q = 1) : d364268 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d364268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d364268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d363819 q = 1) : d364269 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d364269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d364269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d363819 q = 1) : d364270 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d364270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d364270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d363819 q = 1) : d364271 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d364271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d364271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100379 (p : Pattern) (ha : d310053 p = 1) (hb : d363819 p = 1) : d364277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d363819 q = 1) : d364272 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d364272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100378 q ha hb
    | true =>
      simp only [d310048, d364272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d363819 q = 1) : d364273 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d364273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d364273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d363819 q = 1) : d364274 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d364274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d364274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d363819 q = 1) : d364275 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d364275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d364275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d363819 q = 1) : d364276 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d364276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d364276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d363819 q = 1) : d364277 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d364277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d364277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100380 (p : Pattern) (ha : d361629 p = 1) (hb : d363918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d361617 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d361618 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361619 q = 1) (hb : d363912 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43868 q = 1) (hb : d361624 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100185 q ha hb
    | true =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43869 q = 1) (hb : d361625 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43870 q = 1) (hb : d361626 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361627 q = 1) (hb : d363913 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361627, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361627, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d361628 q = 1) (hb : d363914 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361628, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361628, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361432 q = 1) (hb : d363915 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h14 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361433 q = 1) (hb : d363916 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d361434 q = 1) (hb : d363917 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361629 q = 1) (hb : d363918 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361629, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361629, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100381 (p : Pattern) (ha : d361634 p = 1) (hb : d363925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d361432 q = 1) (hb : d363915 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361433 q = 1) (hb : d363916 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d361434 q = 1) (hb : d363917 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361441 q = 1) (hb : d363923 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361442 q = 1) (hb : d363924 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361634 q = 1) (hb : d363925 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361634, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361634, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100382 (p : Pattern) (ha : d361642 p = 1) (hb : d363933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d361432 q = 1) (hb : d363915 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361640 q = 1) (hb : d363931 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361640, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361640, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361641 q = 1) (hb : d363932 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361641, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361641, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361441 q = 1) (hb : d363923 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361442 q = 1) (hb : d363924 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361642 q = 1) (hb : d363933 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361642, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361642, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100383 (p : Pattern) (ha : d361806 p = 1) (hb : d363940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d361308 q = 1) (hb : d363938 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361309 q = 1) (hb : d363939 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361806 q = 1) (hb : d363940 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361806, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361806, d363940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro100384 (p : Pattern) (ha : d361812 p = 1) (hb : d363946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361630 q = 1) (hb : d363919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
    | true =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361631 q = 1) (hb : d363920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361632 q = 1) (hb : d363921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361632, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361632, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361633 q = 1) (hb : d363922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361633, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361633, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361635 q = 1) (hb : d363926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
    | true =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361636 q = 1) (hb : d363927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361637 q = 1) (hb : d363928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361637, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361637, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361638 q = 1) (hb : d363929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361638, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361638, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361639 q = 1) (hb : d363930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361639, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361639, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361645 q = 1) (hb : d363936 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361646 q = 1) (hb : d363937 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361809 q = 1) (hb : d363943 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361810 q = 1) (hb : d363944 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361811 q = 1) (hb : d363945 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361811, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361811, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361812 q = 1) (hb : d363946 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361812, d363946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361812, d363946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100385 (p : Pattern) (ha : d361435 p = 1) (hb : d363947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d361432 q = 1) (hb : d363915 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361432, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361433 q = 1) (hb : d363916 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361433, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d361434 q = 1) (hb : d363917 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361434, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d361308 q = 1) (hb : d363938 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d361309 q = 1) (hb : d363939 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361435 q = 1) (hb : d363947 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361435, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361435, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro100386 (p : Pattern) (ha : d361815 p = 1) (hb : d363954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361436 q = 1) (hb : d363948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
    | true =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361437 q = 1) (hb : d363949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361438 q = 1) (hb : d363950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361438, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361438, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361439 q = 1) (hb : d363951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361439, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361439, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361809 q = 1) (hb : d363943 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361810 q = 1) (hb : d363944 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361813 q = 1) (hb : d363952 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361813, d363952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361813, d363952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361814 q = 1) (hb : d363953 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361815 q = 1) (hb : d363954 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361815, d363954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361815, d363954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100387 (p : Pattern) (ha : d361819 p = 1) (hb : d363958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361809 q = 1) (hb : d363943 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361810 q = 1) (hb : d363944 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361814 q = 1) (hb : d363953 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361819 q = 1) (hb : d363958 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361819, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361819, d363958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100388 (p : Pattern) (ha : d361826 p = 1) (hb : d363965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361816 q = 1) (hb : d363955 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361816, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100384 q ha hb
    | true =>
      simp only [d361816, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100386 q ha hb
  have h2 (q : Pattern) (ha : d361817 q = 1) (hb : d363956 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361817, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361817, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361818 q = 1) (hb : d363957 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361818, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361818, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361820 q = 1) (hb : d363959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100386 q ha hb
    | true =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100387 q ha hb
  have h5 (q : Pattern) (ha : d361821 q = 1) (hb : d363960 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361822 q = 1) (hb : d363961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361823 q = 1) (hb : d363962 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361823, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361823, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361824 q = 1) (hb : d363963 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361824, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361824, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361825 q = 1) (hb : d363964 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361825, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361825, d363964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361826 q = 1) (hb : d363965 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361826, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361826, d363965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100389 (p : Pattern) (ha : d361830 p = 1) (hb : d363969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361820 q = 1) (hb : d363959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100386 q ha hb
    | true =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100387 q ha hb
  have h2 (q : Pattern) (ha : d361821 q = 1) (hb : d363960 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361822 q = 1) (hb : d363961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361824 q = 1) (hb : d363963 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361824, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361824, d363963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361829 q = 1) (hb : d363968 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361829, d363968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361829, d363968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361830 q = 1) (hb : d363969 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361830, d363969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361830, d363969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100390 (p : Pattern) (ha : d361836 p = 1) (hb : d363975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361834 q = 1) (hb : d363973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361835 q = 1) (hb : d363974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361835, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361835, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361836 q = 1) (hb : d363975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361836, d363975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361836, d363975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100391 (p : Pattern) (ha : d361840 p = 1) (hb : d363979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361838 q = 1) (hb : d363977 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361839 q = 1) (hb : d363978 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361839, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361839, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361840 q = 1) (hb : d363979 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361840, d363979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361840, d363979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100392 (p : Pattern) (ha : d361846 p = 1) (hb : d363985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361841 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
    | true =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
  have h2 (q : Pattern) (ha : d361842 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361843 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361844 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361845 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361846 q = 1) (hb : d363985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361846, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361846, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100393 (p : Pattern) (ha : d361849 p = 1) (hb : d363988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361834 q = 1) (hb : d363973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361835 q = 1) (hb : d363974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361835, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361835, d363974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361849 q = 1) (hb : d363988 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361849, d363988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361849, d363988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100394 (p : Pattern) (ha : d361850 p = 1) (hb : d363989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361838 q = 1) (hb : d363977 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361839 q = 1) (hb : d363978 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361839, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361839, d363978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361850 q = 1) (hb : d363989 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361850, d363989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361850, d363989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100395 (p : Pattern) (ha : d361856 p = 1) (hb : d363995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361841 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
    | true =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
  have h2 (q : Pattern) (ha : d361842 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361843 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361844 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361845 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361851 q = 1) (hb : d363990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100393 q ha hb
    | true =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100394 q ha hb
  have h7 (q : Pattern) (ha : d361852 q = 1) (hb : d363991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361852, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361852, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361853 q = 1) (hb : d363992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361853, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361853, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361854 q = 1) (hb : d363993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361854, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361854, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361855 q = 1) (hb : d363994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361855, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361855, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361856 q = 1) (hb : d363995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361856, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361856, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100396 (p : Pattern) (ha : d361861 p = 1) (hb : d364000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361834 q = 1) (hb : d363973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361860 q = 1) (hb : d363999 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361860, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361860, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361861 q = 1) (hb : d364000 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361861, d364000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361861, d364000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100397 (p : Pattern) (ha : d361863 p = 1) (hb : d364002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361838 q = 1) (hb : d363977 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361862 q = 1) (hb : d364001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361862, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361862, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361863 q = 1) (hb : d364002 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361863, d364002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361863, d364002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100398 (p : Pattern) (ha : d361870 p = 1) (hb : d364009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361868 q = 1) (hb : d364007 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361868, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361868, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361869 q = 1) (hb : d364008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361869, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361869, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361870 q = 1) (hb : d364009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361870, d364009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361870, d364009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100399 (p : Pattern) (ha : d361873 p = 1) (hb : d364012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361871 q = 1) (hb : d364010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361871, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361871, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361872 q = 1) (hb : d364011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361872, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361872, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361873 q = 1) (hb : d364012 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361873, d364012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361873, d364012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100400 (p : Pattern) (ha : d361891 p = 1) (hb : d364020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d361617 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d361618 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43405 q = 1) (hb : d361877 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43405, d361877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43405, d361877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361881 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d361883 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100178 q ha hb
    | true =>
      simp only [d43846, d361883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d361884 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d361884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d361885 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43848, d361885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361886 q = 1) (hb : d364016 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361886, d364016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361886, d364016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d361887 q = 1) (hb : d364017 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361887, d364017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361887, d364017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361619 q = 1) (hb : d363912 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43859 q = 1) (hb : d361888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43859, d361888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43859, d361888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361889 q = 1) (hb : d364018 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361889, d364018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361889, d364018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d361890 q = 1) (hb : d364019 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361890, d364019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361890, d364019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361891 q = 1) (hb : d364020 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361891, d364020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361891, d364020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100401 (p : Pattern) (ha : d361905 p = 1) (hb : d364028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d361617 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d361618 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d361430 q = 1) (hb : d363910 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100182 q hb ha
    | true =>
      simp only [d361430, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361431 q = 1) (hb : d363911 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361431, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361619 q = 1) (hb : d363912 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361619, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43868 q = 1) (hb : d361624 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100185 q ha hb
    | true =>
      simp only [d43868, d361624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43869 q = 1) (hb : d361625 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43869, d361625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43870 q = 1) (hb : d361626 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43870, d361626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361627 q = 1) (hb : d363913 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361627, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361627, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d361628 q = 1) (hb : d363914 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361628, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361628, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d43886 q = 1) (hb : d361900 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43887 q = 1) (hb : d361901 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d361902 q = 1) (hb : d364025 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361902, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d361902, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h16 (q : Pattern) (ha : d361903 q = 1) (hb : d364026 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361903, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361903, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d361904 q = 1) (hb : d364027 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361904, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361904, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361905 q = 1) (hb : d364028 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361905, d364028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361905, d364028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100402 (p : Pattern) (ha : d361914 p = 1) (hb : d364034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d361617 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100181 q ha hb
    | true =>
      simp only [d42937, d361617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d361618 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, d361618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43886 q = 1) (hb : d361900 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100186 q ha hb
    | true =>
      simp only [d43886, d361900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43887 q = 1) (hb : d361901 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43887, d361901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43995 q = 1) (hb : d361911 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43995, d361911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43995, d361911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43996 q = 1) (hb : d361912 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43996, d361912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43996, d361912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43997 q = 1) (hb : d361913 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43997, d361913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43997, d361913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d361902 q = 1) (hb : d364025 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d361902, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361902, d364025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361903 q = 1) (hb : d364026 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361903, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361903, d364026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361904 q = 1) (hb : d364027 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361904, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361904, d364027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361914 q = 1) (hb : d364034 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361914, d364034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d361914, d364034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100403 (p : Pattern) (ha : d361920 p = 1) (hb : d364040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361892 q = 1) (hb : d364021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361892, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100400 q ha hb
    | true =>
      simp only [d361892, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361893 q = 1) (hb : d364022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361893, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361893, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361894 q = 1) (hb : d364023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361894, d364023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361894, d364023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361895 q = 1) (hb : d364024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361895, d364024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361895, d364024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361906 q = 1) (hb : d364029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361906, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100401 q ha hb
    | true =>
      simp only [d361906, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361907 q = 1) (hb : d364030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361907, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361907, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361908 q = 1) (hb : d364031 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361908, d364031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361908, d364031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361909 q = 1) (hb : d364032 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361909, d364032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361909, d364032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361910 q = 1) (hb : d364033 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361910, d364033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361910, d364033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361915 q = 1) (hb : d364035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361915, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100402 q ha hb
    | true =>
      simp only [d361915, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361916 q = 1) (hb : d364036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361916, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361916, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361917 q = 1) (hb : d364037 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361917, d364037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361917, d364037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361918 q = 1) (hb : d364038 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361918, d364038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361918, d364038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361645 q = 1) (hb : d363936 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361646 q = 1) (hb : d363937 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361919 q = 1) (hb : d364039 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361919, d364039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361919, d364039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361920 q = 1) (hb : d364040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361920, d364040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361920, d364040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100404 (p : Pattern) (ha : d361924 p = 1) (hb : d364044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361645 q = 1) (hb : d363936 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361646 q = 1) (hb : d363937 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361809 q = 1) (hb : d363943 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361809, d363943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361810 q = 1) (hb : d363944 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361810, d363944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361811 q = 1) (hb : d363945 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361811, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361811, d363945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361814 q = 1) (hb : d363953 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361814, d363953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361924 q = 1) (hb : d364044 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361924, d364044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361924, d364044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100405 (p : Pattern) (ha : d361930 p = 1) (hb : d364050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361921 q = 1) (hb : d364041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361921, d364041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100403 q ha hb
    | true =>
      simp only [d361921, d364041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100384 q ha hb
  have h2 (q : Pattern) (ha : d361922 q = 1) (hb : d364042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361922, d364042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361922, d364042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361923 q = 1) (hb : d364043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361923, d364043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361923, d364043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361925 q = 1) (hb : d364045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361925, d364045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100384 q ha hb
    | true =>
      simp only [d361925, d364045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100404 q ha hb
  have h5 (q : Pattern) (ha : d361926 q = 1) (hb : d364046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361926, d364046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361926, d364046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361927 q = 1) (hb : d364047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361927, d364047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361927, d364047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361928 q = 1) (hb : d364048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361928, d364048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361928, d364048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361816 q = 1) (hb : d363955 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361816, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100384 q ha hb
    | true =>
      simp only [d361816, d363955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100386 q ha hb
  have h9 (q : Pattern) (ha : d361817 q = 1) (hb : d363956 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361817, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361817, d363956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361818 q = 1) (hb : d363957 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361818, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361818, d363957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361820 q = 1) (hb : d363959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100386 q ha hb
    | true =>
      simp only [d361820, d363959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100387 q ha hb
  have h12 (q : Pattern) (ha : d361821 q = 1) (hb : d363960 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361821, d363960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361822 q = 1) (hb : d363961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361822, d363961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361823 q = 1) (hb : d363962 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361823, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361823, d363962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361929 q = 1) (hb : d364049 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361929, d364049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361929, d364049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361930 q = 1) (hb : d364050 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361930, d364050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361930, d364050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100406 (p : Pattern) (ha : d361936 p = 1) (hb : d364056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361931 q = 1) (hb : d364051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361931, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100405 q ha hb
    | true =>
      simp only [d361931, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361932 q = 1) (hb : d364052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361932, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361932, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361933 q = 1) (hb : d364053 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361933, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361933, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361934 q = 1) (hb : d364054 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361934, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361934, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361935 q = 1) (hb : d364055 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361935, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361935, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361936 q = 1) (hb : d364056 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361936, d364056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361936, d364056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100407 (p : Pattern) (ha : d361942 p = 1) (hb : d364062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361939 q = 1) (hb : d364059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361939, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361939, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361940 q = 1) (hb : d364060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361940, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361940, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361941 q = 1) (hb : d364061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361941, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361941, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361942 q = 1) (hb : d364062 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361942, d364062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361942, d364062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100408 (p : Pattern) (ha : d361948 p = 1) (hb : d364068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361864 q = 1) (hb : d364003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361864, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100396 q ha hb
    | true =>
      simp only [d361864, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100397 q ha hb
  have h2 (q : Pattern) (ha : d361865 q = 1) (hb : d364004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361865, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361865, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361866 q = 1) (hb : d364005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361866, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361866, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361867 q = 1) (hb : d364006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361867, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361867, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361874 q = 1) (hb : d364013 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361874, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100398 q ha hb
    | true =>
      simp only [d361874, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100399 q ha hb
  have h6 (q : Pattern) (ha : d361875 q = 1) (hb : d364014 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361875, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361875, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361876 q = 1) (hb : d364015 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361876, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361876, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361937 q = 1) (hb : d364057 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361937, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100406 q ha hb
    | true =>
      simp only [d361937, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361841 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361938 q = 1) (hb : d364058 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361938, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361938, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361943 q = 1) (hb : d364063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361943, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100407 q ha hb
    | true =>
      simp only [d361943, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361944 q = 1) (hb : d364064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361944, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361944, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361945 q = 1) (hb : d364065 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361945, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361945, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361946 q = 1) (hb : d364066 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361946, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361946, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361947 q = 1) (hb : d364067 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361947, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361947, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361948 q = 1) (hb : d364068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361948, d364068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361948, d364068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100409 (p : Pattern) (ha : d361949 p = 1) (hb : d364069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361834 q = 1) (hb : d363973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361834, d363973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361860 q = 1) (hb : d363999 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361860, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361860, d363999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361949 q = 1) (hb : d364069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361949, d364069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361949, d364069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100410 (p : Pattern) (ha : d361950 p = 1) (hb : d364070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361838 q = 1) (hb : d363977 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361838, d363977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361862 q = 1) (hb : d364001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361862, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361862, d364001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361950 q = 1) (hb : d364070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361950, d364070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361950, d364070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100411 (p : Pattern) (ha : d361955 p = 1) (hb : d364075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361833 q = 1) (hb : d363972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361833, d363972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361868 q = 1) (hb : d364007 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361868, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361868, d364007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361869 q = 1) (hb : d364008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361869, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361869, d364008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361955 q = 1) (hb : d364075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361955, d364075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361955, d364075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100412 (p : Pattern) (ha : d361956 p = 1) (hb : d364076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361831 q = 1) (hb : d363970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100389 q ha hb
    | true =>
      simp only [d361831, d363970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361832 q = 1) (hb : d363971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361832, d363971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361837 q = 1) (hb : d363976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361837, d363976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361871 q = 1) (hb : d364010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361871, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361871, d364010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361872 q = 1) (hb : d364011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361872, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361872, d364011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361956 q = 1) (hb : d364076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361956, d364076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361956, d364076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100413 (p : Pattern) (ha : d361960 p = 1) (hb : d364080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361931 q = 1) (hb : d364051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361931, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100405 q ha hb
    | true =>
      simp only [d361931, d364051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361932 q = 1) (hb : d364052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361932, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361932, d364052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361933 q = 1) (hb : d364053 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361933, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361933, d364053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361934 q = 1) (hb : d364054 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361934, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361934, d364054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361935 q = 1) (hb : d364055 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361935, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361935, d364055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361960 q = 1) (hb : d364080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361960, d364080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361960, d364080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100414 (p : Pattern) (ha : d361963 p = 1) (hb : d364083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361827 q = 1) (hb : d363966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100388 q ha hb
    | true =>
      simp only [d361827, d363966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361828 q = 1) (hb : d363967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361828, d363967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361939 q = 1) (hb : d364059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361939, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361939, d364059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361940 q = 1) (hb : d364060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361940, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361940, d364060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361941 q = 1) (hb : d364061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361941, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361941, d364061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361963 q = 1) (hb : d364083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361963, d364083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361963, d364083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100415 (p : Pattern) (ha : d361969 p = 1) (hb : d364089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361864 q = 1) (hb : d364003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361864, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100396 q ha hb
    | true =>
      simp only [d361864, d364003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100397 q ha hb
  have h2 (q : Pattern) (ha : d361865 q = 1) (hb : d364004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361865, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361865, d364004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361866 q = 1) (hb : d364005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361866, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361866, d364005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361867 q = 1) (hb : d364006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361867, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361867, d364006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361874 q = 1) (hb : d364013 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361874, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100398 q ha hb
    | true =>
      simp only [d361874, d364013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100399 q ha hb
  have h6 (q : Pattern) (ha : d361875 q = 1) (hb : d364014 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361875, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361875, d364014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361876 q = 1) (hb : d364015 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361876, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361876, d364015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361937 q = 1) (hb : d364057 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361937, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100406 q ha hb
    | true =>
      simp only [d361937, d364057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361841 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361938 q = 1) (hb : d364058 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361938, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361938, d364058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361943 q = 1) (hb : d364063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361943, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100407 q ha hb
    | true =>
      simp only [d361943, d364063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361944 q = 1) (hb : d364064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361944, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361944, d364064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361945 q = 1) (hb : d364065 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361945, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361945, d364065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361946 q = 1) (hb : d364066 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361946, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361946, d364066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361947 q = 1) (hb : d364067 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361947, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361947, d364067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361951 q = 1) (hb : d364071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361951, d364071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100409 q ha hb
    | true =>
      simp only [d361951, d364071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100410 q ha hb
  have h17 (q : Pattern) (ha : d361952 q = 1) (hb : d364072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361952, d364072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361952, d364072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361953 q = 1) (hb : d364073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361953, d364073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361953, d364073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361954 q = 1) (hb : d364074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361954, d364074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361954, d364074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361957 q = 1) (hb : d364077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361957, d364077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100411 q ha hb
    | true =>
      simp only [d361957, d364077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100412 q ha hb
  have h21 (q : Pattern) (ha : d361958 q = 1) (hb : d364078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361958, d364078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361958, d364078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d361959 q = 1) (hb : d364079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361959, d364079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361959, d364079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361961 q = 1) (hb : d364081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361961, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100413 q ha hb
    | true =>
      simp only [d361961, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100393 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d361851 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d361962 q = 1) (hb : d364082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361962, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d361962, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d361964 q = 1) (hb : d364084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361964, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100414 q ha hb
    | true =>
      simp only [d361964, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d361965 q = 1) (hb : d364085 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361965, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d361965, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d361966 q = 1) (hb : d364086 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361966, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d361966, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d361967 q = 1) (hb : d364087 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361967, d364087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361967, d364087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d361968 q = 1) (hb : d364088 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361968, d364088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361968, d364088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d361969 q = 1) (hb : d364089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361969, d364089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361969, d364089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100416 (p : Pattern) (ha : d361976 p = 1) (hb : d364096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361841 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
    | true =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
  have h2 (q : Pattern) (ha : d361842 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361842, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361843 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361843, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361844 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361844, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361845 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361845, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361971 q = 1) (hb : d364091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361971, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
    | true =>
      simp only [d361971, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361972 q = 1) (hb : d364092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361972, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361972, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361973 q = 1) (hb : d364093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361973, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361973, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361974 q = 1) (hb : d364094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361974, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361974, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361975 q = 1) (hb : d364095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361975, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361975, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361976 q = 1) (hb : d364096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361976, d364096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361976, d364096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100417 (p : Pattern) (ha : d361982 p = 1) (hb : d364102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361971 q = 1) (hb : d364091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361971, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
    | true =>
      simp only [d361971, d364091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361972 q = 1) (hb : d364092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361972, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361972, d364092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361973 q = 1) (hb : d364093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361973, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361973, d364093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361974 q = 1) (hb : d364094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361974, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361974, d364094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361975 q = 1) (hb : d364095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361975, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361975, d364095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361977 q = 1) (hb : d364097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361977, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100394 q ha hb
    | true =>
      simp only [d361977, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361978 q = 1) (hb : d364098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361978, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361978, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361979 q = 1) (hb : d364099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361979, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361979, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361980 q = 1) (hb : d364100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361980, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361980, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361981 q = 1) (hb : d364101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361981, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361981, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361982 q = 1) (hb : d364102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361982, d364102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361982, d364102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100418 (p : Pattern) (ha : d361989 p = 1) (hb : d364109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361961 q = 1) (hb : d364081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361961, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100413 q ha hb
    | true =>
      simp only [d361961, d364081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100393 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361851 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361962 q = 1) (hb : d364082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361962, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361962, d364082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361964 q = 1) (hb : d364084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361964, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100414 q ha hb
    | true =>
      simp only [d361964, d364084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361965 q = 1) (hb : d364085 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361965, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361965, d364085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361966 q = 1) (hb : d364086 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361966, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361966, d364086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361987 q = 1) (hb : d364107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361987, d364107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361987, d364107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361988 q = 1) (hb : d364108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361988, d364108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361988, d364108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361989 q = 1) (hb : d364109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361989, d364109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361989, d364109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100419 (p : Pattern) (ha : d361991 p = 1) (hb : d364111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361977 q = 1) (hb : d364097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361977, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100394 q ha hb
    | true =>
      simp only [d361977, d364097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361978 q = 1) (hb : d364098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361978, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361978, d364098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361979 q = 1) (hb : d364099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361979, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361979, d364099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361980 q = 1) (hb : d364100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361980, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361980, d364100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361981 q = 1) (hb : d364101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361981, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361981, d364101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361991 q = 1) (hb : d364111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361991, d364111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361991, d364111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100420 (p : Pattern) (ha : d362011 p = 1) (hb : d364135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361997 q = 1) (hb : d364117 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361997, d364117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361997, d364117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100400 q ha hb
  have h2 (q : Pattern) (ha : d361892 q = 1) (hb : d364021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361892, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100400 q ha hb
    | true =>
      simp only [d361892, d364021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361998 q = 1) (hb : d364118 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361998, d364118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361998, d364118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361893 q = 1) (hb : d364022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361893, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361893, d364022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361999 q = 1) (hb : d364119 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361999, d364119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361999, d364119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362000 q = 1) (hb : d364120 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362000, d364120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362000, d364120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362001 q = 1) (hb : d364121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362001, d364121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362001, d364121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100401 q ha hb
  have h8 (q : Pattern) (ha : d361906 q = 1) (hb : d364029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361906, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100401 q ha hb
    | true =>
      simp only [d361906, d364029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362002 q = 1) (hb : d364122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362002, d364122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362002, d364122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361907 q = 1) (hb : d364030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361907, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361907, d364030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362003 q = 1) (hb : d364123 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362003, d364123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362003, d364123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362004 q = 1) (hb : d364124 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362004, d364124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362004, d364124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362005 q = 1) (hb : d364125 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362005, d364125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362005, d364125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362006 q = 1) (hb : d364126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362006, d364126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362006, d364126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100402 q ha hb
  have h15 (q : Pattern) (ha : d361915 q = 1) (hb : d364035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361915, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100402 q ha hb
    | true =>
      simp only [d361915, d364035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d362007 q = 1) (hb : d364127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362007, d364127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362007, d364127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361916 q = 1) (hb : d364036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361916, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361916, d364036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d362008 q = 1) (hb : d364128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362008, d364128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362008, d364128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d362009 q = 1) (hb : d364129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362009, d364129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d362009, d364129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d361734 q = 1) (hb : d364130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
  have h21 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d361735 q = 1) (hb : d364131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d361736 q = 1) (hb : d364132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d361737 q = 1) (hb : d364133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d362010 q = 1) (hb : d364134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362010, d364134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362010, d364134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d362011 q = 1) (hb : d364135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362011, d364135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362011, d364135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100421 (p : Pattern) (ha : d362017 p = 1) (hb : d364150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361725 q = 1) (hb : d364136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361725, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361725, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
  have h2 (q : Pattern) (ha : d361630 q = 1) (hb : d363919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
    | true =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361726 q = 1) (hb : d364137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361726, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361726, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361631 q = 1) (hb : d363920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361727 q = 1) (hb : d364138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361727, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361727, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361728 q = 1) (hb : d364139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361728, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361728, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361729 q = 1) (hb : d364140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361729, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361729, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
  have h8 (q : Pattern) (ha : d361635 q = 1) (hb : d363926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
    | true =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361730 q = 1) (hb : d364141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361730, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361730, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361636 q = 1) (hb : d363927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361731 q = 1) (hb : d364142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361731, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361731, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361732 q = 1) (hb : d364143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361732, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361732, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361733 q = 1) (hb : d364144 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361733, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361733, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361734 q = 1) (hb : d364130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
  have h15 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361735 q = 1) (hb : d364131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361736 q = 1) (hb : d364132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361737 q = 1) (hb : d364133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d362012 q = 1) (hb : d364145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
  have h21 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d362013 q = 1) (hb : d364146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d362014 q = 1) (hb : d364147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d362015 q = 1) (hb : d364148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d362016 q = 1) (hb : d364149 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362016, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362016, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d362017 q = 1) (hb : d364150 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362017, d364150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362017, d364150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100422 (p : Pattern) (ha : d362022 p = 1) (hb : d364155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361734 q = 1) (hb : d364130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
  have h2 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361735 q = 1) (hb : d364131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361736 q = 1) (hb : d364132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361737 q = 1) (hb : d364133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362012 q = 1) (hb : d364145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
  have h8 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362013 q = 1) (hb : d364146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362014 q = 1) (hb : d364147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362015 q = 1) (hb : d364148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362016 q = 1) (hb : d364149 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362016, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362016, d364149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362021 q = 1) (hb : d364154 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362022 q = 1) (hb : d364155 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362022, d364155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362022, d364155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100423 (p : Pattern) (ha : d362028 p = 1) (hb : d364165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361509 q = 1) (hb : d364160 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361509, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361509, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
  have h2 (q : Pattern) (ha : d361436 q = 1) (hb : d363948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
    | true =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361510 q = 1) (hb : d364161 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361510, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361510, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361437 q = 1) (hb : d363949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361511 q = 1) (hb : d364162 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361511, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361511, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361512 q = 1) (hb : d364163 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361512, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361512, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362012 q = 1) (hb : d364145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
  have h8 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362013 q = 1) (hb : d364146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d362014 q = 1) (hb : d364147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362015 q = 1) (hb : d364148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d362027 q = 1) (hb : d364164 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362027, d364164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362027, d364164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362021 q = 1) (hb : d364154 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d362028 q = 1) (hb : d364165 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362028, d364165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362028, d364165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100424 (p : Pattern) (ha : d362032 p = 1) (hb : d364169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362012 q = 1) (hb : d364145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362012, d364145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
  have h2 (q : Pattern) (ha : d361807 q = 1) (hb : d363941 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100383 q ha hb
    | true =>
      simp only [d361807, d363941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d362013 q = 1) (hb : d364146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362013, d364146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361808 q = 1) (hb : d363942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361808, d363942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362014 q = 1) (hb : d364147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362014, d364147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362015 q = 1) (hb : d364148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362015, d364148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362021 q = 1) (hb : d364154 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362021, d364154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362032 q = 1) (hb : d364169 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d362032, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362032, d364169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100425 (p : Pattern) (ha : d362038 p = 1) (hb : d364175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362018 q = 1) (hb : d364151 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362018, d364151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100420 q ha hb
    | true =>
      simp only [d362018, d364151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100421 q ha hb
  have h2 (q : Pattern) (ha : d362019 q = 1) (hb : d364152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362019, d364152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362019, d364152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362020 q = 1) (hb : d364153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362020, d364153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362020, d364153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362023 q = 1) (hb : d364156 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362023, d364156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100421 q ha hb
    | true =>
      simp only [d362023, d364156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100422 q ha hb
  have h5 (q : Pattern) (ha : d362024 q = 1) (hb : d364157 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362024, d364157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362024, d364157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362025 q = 1) (hb : d364158 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362025, d364158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362025, d364158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362026 q = 1) (hb : d364159 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362026, d364159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362026, d364159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362029 q = 1) (hb : d364166 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362029, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100421 q ha hb
    | true =>
      simp only [d362029, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100423 q ha hb
  have h9 (q : Pattern) (ha : d362030 q = 1) (hb : d364167 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362030, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362030, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362031 q = 1) (hb : d364168 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362031, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362031, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d362033 q = 1) (hb : d364170 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100423 q ha hb
    | true =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100424 q ha hb
  have h12 (q : Pattern) (ha : d362034 q = 1) (hb : d364171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362035 q = 1) (hb : d364172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d362036 q = 1) (hb : d364173 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362036, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362036, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d362037 q = 1) (hb : d364174 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362037, d364174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362037, d364174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d362038 q = 1) (hb : d364175 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362038, d364175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362038, d364175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100426 (p : Pattern) (ha : d362043 p = 1) (hb : d364180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362029 q = 1) (hb : d364166 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362029, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100421 q ha hb
    | true =>
      simp only [d362029, d364166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100423 q ha hb
  have h2 (q : Pattern) (ha : d362030 q = 1) (hb : d364167 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362030, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362030, d364167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362031 q = 1) (hb : d364168 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362031, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362031, d364168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362033 q = 1) (hb : d364170 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100423 q ha hb
    | true =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100424 q ha hb
  have h5 (q : Pattern) (ha : d362034 q = 1) (hb : d364171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362035 q = 1) (hb : d364172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362036 q = 1) (hb : d364173 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362036, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362036, d364173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362041 q = 1) (hb : d364178 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362041, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362041, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d362042 q = 1) (hb : d364179 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362042, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362042, d364179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362043 q = 1) (hb : d364180 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362043, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362043, d364180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100427 (p : Pattern) (ha : d362049 p = 1) (hb : d364186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362039 q = 1) (hb : d364176 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362039, d364176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100425 q ha hb
    | true =>
      simp only [d362039, d364176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362040 q = 1) (hb : d364177 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362040, d364177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362040, d364177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362044 q = 1) (hb : d364181 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100426 q ha hb
    | true =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362045 q = 1) (hb : d364182 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362046 q = 1) (hb : d364183 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362046, d364183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362046, d364183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362047 q = 1) (hb : d364184 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362047, d364184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362047, d364184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362048 q = 1) (hb : d364185 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362048, d364185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362048, d364185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362049 q = 1) (hb : d364186 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362049, d364186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362049, d364186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100428 (p : Pattern) (ha : d362051 p = 1) (hb : d364188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362033 q = 1) (hb : d364170 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100423 q ha hb
    | true =>
      simp only [d362033, d364170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100424 q ha hb
  have h2 (q : Pattern) (ha : d362034 q = 1) (hb : d364171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362034, d364171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362035 q = 1) (hb : d364172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362035, d364172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362041 q = 1) (hb : d364178 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d362041, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362041, d364178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362050 q = 1) (hb : d364187 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d362050, d364187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362050, d364187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362051 q = 1) (hb : d364188 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d362051, d364188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362051, d364188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100429 (p : Pattern) (ha : d362057 p = 1) (hb : d364194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362044 q = 1) (hb : d364181 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100426 q ha hb
    | true =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362045 q = 1) (hb : d364182 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362052 q = 1) (hb : d364189 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362052, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100428 q ha hb
    | true =>
      simp only [d362052, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362053 q = 1) (hb : d364190 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362053, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362053, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362054 q = 1) (hb : d364191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362054, d364191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362054, d364191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362055 q = 1) (hb : d364192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362055, d364192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362055, d364192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d362056 q = 1) (hb : d364193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362056, d364193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362056, d364193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d362057 q = 1) (hb : d364194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362057, d364194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362057, d364194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100430 (p : Pattern) (ha : d362068 p = 1) (hb : d364200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362044 q = 1) (hb : d364181 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100426 q ha hb
    | true =>
      simp only [d362044, d364181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362045 q = 1) (hb : d364182 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362045, d364182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362065 q = 1) (hb : d364197 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362065, d364197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362065, d364197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362066 q = 1) (hb : d364198 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362066, d364198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362066, d364198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362067 q = 1) (hb : d364199 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362067, d364199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362067, d364199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362068 q = 1) (hb : d364200 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362068, d364200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362068, d364200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100431 (p : Pattern) (ha : d362074 p = 1) (hb : d364206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362058 q = 1) (hb : d364195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362058, d364195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100427 q ha hb
    | true =>
      simp only [d362058, d364195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100429 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d362063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362064 q = 1) (hb : d364196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362064, d364196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362064, d364196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d362069 q = 1) (hb : d364201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362069, d364201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100430 q ha hb
    | true =>
      simp only [d362069, d364201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362070 q = 1) (hb : d364202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362070, d364202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362070, d364202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362071 q = 1) (hb : d364203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362071, d364203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362071, d364203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362072 q = 1) (hb : d364204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362072, d364204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362072, d364204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362073 q = 1) (hb : d364205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362073, d364205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362073, d364205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362074 q = 1) (hb : d364206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362074, d364206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362074, d364206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100432 (p : Pattern) (ha : d362062 p = 1) (hb : d364211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362052 q = 1) (hb : d364189 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362052, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100428 q ha hb
    | true =>
      simp only [d362052, d364189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362053 q = 1) (hb : d364190 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d362053, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362053, d364190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362059 q = 1) (hb : d364208 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d362059, d364208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362059, d364208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362060 q = 1) (hb : d364209 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d362060, d364209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362060, d364209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d362061 q = 1) (hb : d364210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d362061, d364210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362061, d364210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d362062 q = 1) (hb : d364211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d362062, d364211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362062, d364211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100433 (p : Pattern) (ha : d362081 p = 1) (hb : d364217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362076 q = 1) (hb : d364212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362076, d364212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100432 q ha hb
    | true =>
      simp only [d362076, d364212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d362077 q = 1) (hb : d364213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362077, d364213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362077, d364213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362078 q = 1) (hb : d364214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362078, d364214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362078, d364214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d362079 q = 1) (hb : d364215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362079, d364215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362079, d364215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362080 q = 1) (hb : d364216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362080, d364216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362080, d364216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362081 q = 1) (hb : d364217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362081, d364217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362081, d364217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100434 (p : Pattern) (ha : d362087 p = 1) (hb : d364223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361847 q = 1) (hb : d363986 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361847, d363986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361847, d363986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100392 q ha hb
  have h2 (q : Pattern) (ha : d361848 q = 1) (hb : d363987 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361848, d363987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361848, d363987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361857 q = 1) (hb : d363996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361857, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100392 q ha hb
    | true =>
      simp only [d361857, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100395 q ha hb
  have h4 (q : Pattern) (ha : d361858 q = 1) (hb : d363997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361858, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361858, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361859 q = 1) (hb : d363998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361859, d363998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361859, d363998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361970 q = 1) (hb : d364090 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361970, d364090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100408 q ha hb
    | true =>
      simp only [d361970, d364090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100415 q ha hb
  have h7 (q : Pattern) (ha : d361983 q = 1) (hb : d364103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361983, d364103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100416 q ha hb
    | true =>
      simp only [d361983, d364103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100417 q ha hb
  have h8 (q : Pattern) (ha : d361984 q = 1) (hb : d364104 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361984, d364104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361984, d364104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361985 q = 1) (hb : d364105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361985, d364105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361985, d364105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361986 q = 1) (hb : d364106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361986, d364106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361986, d364106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361990 q = 1) (hb : d364110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361990, d364110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361990, d364110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100418 q ha hb
  have h12 (q : Pattern) (ha : d361992 q = 1) (hb : d364112 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361992, d364112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361992, d364112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100419 q ha hb
  have h13 (q : Pattern) (ha : d361993 q = 1) (hb : d364113 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361993, d364113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361993, d364113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361994 q = 1) (hb : d364114 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361994, d364114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361994, d364114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361995 q = 1) (hb : d364115 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361995, d364115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361995, d364115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361996 q = 1) (hb : d364116 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361996, d364116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361996, d364116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362075 q = 1) (hb : d364207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362075, d364207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362075, d364207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100431 q ha hb
  have h18 (q : Pattern) (ha : d362082 q = 1) (hb : d364218 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362082, d364218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362082, d364218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100433 q ha hb
  have h19 (q : Pattern) (ha : d362083 q = 1) (hb : d364219 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362083, d364219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d362083, d364219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d362084 q = 1) (hb : d364220 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362084, d364220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d362084, d364220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d362085 q = 1) (hb : d364221 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362085, d364221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d362085, d364221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d362086 q = 1) (hb : d364222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362086, d364222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d362086, d364222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d362087 q = 1) (hb : d364223 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d362087, d364223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362087, d364223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100435 (p : Pattern) (ha : d362093 p = 1) (hb : d364229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362088 q = 1) (hb : d364224 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d362088, d364224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362088, d364224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100434 q ha hb
  have h2 (q : Pattern) (ha : d362089 q = 1) (hb : d364225 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d362089, d364225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362089, d364225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362090 q = 1) (hb : d364226 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d362090, d364226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362090, d364226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362091 q = 1) (hb : d364227 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d362091, d364227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362091, d364227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362092 q = 1) (hb : d364228 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d362092, d364228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362092, d364228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362093 q = 1) (hb : d364229 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d362093, d364229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362093, d364229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100436 (p : Pattern) (ha : d363867 p = 1) (hb : d364235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362094 q = 1) (hb : d364230 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d362094, d364230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362094, d364230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100435 q ha hb
  have h4 (q : Pattern) (ha : d362095 q = 1) (hb : d364231 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d362095, d364231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362095, d364231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362095 q = 1) (hb : d364232 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363865 q = 1) (hb : d364233 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363865, d364233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363865, d364233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d363866 q = 1) (hb : d364234 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363866, d364234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363866, d364234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d363867 q = 1) (hb : d364235 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363867, d364235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363867, d364235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100437 (p : Pattern) (ha : d363873 p = 1) (hb : d364241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363868 q = 1) (hb : d364236 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363868, d364236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100436 q ha hb
    | true =>
      simp only [d363868, d364236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363869 q = 1) (hb : d364237 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363869, d364237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363869, d364237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363870 q = 1) (hb : d364238 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363870, d364238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363870, d364238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363871 q = 1) (hb : d364239 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363871, d364239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363871, d364239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363872 q = 1) (hb : d364240 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363872, d364240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363872, d364240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363873 q = 1) (hb : d364241 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363873, d364241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363873, d364241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100438 (p : Pattern) (ha : d363879 p = 1) (hb : d364247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363874 q = 1) (hb : d364242 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363874, d364242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100437 q ha hb
    | true =>
      simp only [d363874, d364242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363875 q = 1) (hb : d364243 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363875, d364243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363875, d364243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363876 q = 1) (hb : d364244 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363876, d364244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363876, d364244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363877 q = 1) (hb : d364245 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363877, d364245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363877, d364245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363878 q = 1) (hb : d364246 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363878, d364246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363878, d364246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363879 q = 1) (hb : d364247 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363879, d364247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363879, d364247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100439 (p : Pattern) (ha : d363885 p = 1) (hb : d364253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363880 q = 1) (hb : d364248 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363880, d364248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100438 q ha hb
    | true =>
      simp only [d363880, d364248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363881 q = 1) (hb : d364249 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363881, d364249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363881, d364249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363882 q = 1) (hb : d364250 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363882, d364250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363882, d364250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363883 q = 1) (hb : d364251 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363883, d364251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363883, d364251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363884 q = 1) (hb : d364252 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363884, d364252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363884, d364252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363885 q = 1) (hb : d364253 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363885, d364253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363885, d364253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100440 (p : Pattern) (ha : d363891 p = 1) (hb : d364259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363886 q = 1) (hb : d364254 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363886, d364254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100439 q ha hb
    | true =>
      simp only [d363886, d364254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363887 q = 1) (hb : d364255 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363887, d364255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363887, d364255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363888 q = 1) (hb : d364256 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363888, d364256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363888, d364256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363889 q = 1) (hb : d364257 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363889, d364257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363889, d364257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363890 q = 1) (hb : d364258 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363890, d364258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363890, d364258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363891 q = 1) (hb : d364259 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363891, d364259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363891, d364259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100441 (p : Pattern) (ha : d363897 p = 1) (hb : d364265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363892 q = 1) (hb : d364260 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363892, d364260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100440 q ha hb
    | true =>
      simp only [d363892, d364260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363893 q = 1) (hb : d364261 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363893, d364261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363893, d364261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363894 q = 1) (hb : d364262 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363894, d364262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363894, d364262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363895 q = 1) (hb : d364263 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363895, d364263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363895, d364263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363896 q = 1) (hb : d364264 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363896, d364264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363896, d364264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363897 q = 1) (hb : d364265 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363897, d364265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363897, d364265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100442 (p : Pattern) (ha : d363903 p = 1) (hb : d364271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363898 q = 1) (hb : d364266 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363898, d364266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100441 q ha hb
    | true =>
      simp only [d363898, d364266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363899 q = 1) (hb : d364267 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363899, d364267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363899, d364267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363900 q = 1) (hb : d364268 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363900, d364268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363900, d364268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363901 q = 1) (hb : d364269 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363901, d364269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363901, d364269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363902 q = 1) (hb : d364270 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363902, d364270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363902, d364270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363903 q = 1) (hb : d364271 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363903, d364271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363903, d364271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100443 (p : Pattern) (ha : d363909 p = 1) (hb : d364277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363904 q = 1) (hb : d364272 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363904, d364272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100442 q ha hb
    | true =>
      simp only [d363904, d364272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363905 q = 1) (hb : d364273 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363905, d364273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363905, d364273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363906 q = 1) (hb : d364274 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363906, d364274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363906, d364274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363907 q = 1) (hb : d364275 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363907, d364275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363907, d364275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363908 q = 1) (hb : d364276 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363908, d364276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363908, d364276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363909 q = 1) (hb : d364277 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363909, d364277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363909, d364277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100444 (p : Pattern) (ha : d308 p = 1) (hb : d357498 p = 1) : d364280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43379 q = 1) : d363990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100322 q ha hb
    | true =>
      simp only [d43379, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100323 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43380 q = 1) : d363991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43380, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43381 q = 1) : d363992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43381, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43382 q = 1) : d363993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43382, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43383 q = 1) : d363994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43383, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357498 q = 1) : d364280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357498, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357498, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100445 (p : Pattern) (ha : d308 p = 1) (hb : d357509 p = 1) : d364291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357504 q = 1) : d364286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357504, d364286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100365 q ha hb
    | true =>
      simp only [d357504, d364286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100331 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357505 q = 1) : d364287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357505, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357505, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357506 q = 1) : d364288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357506, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357506, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357507 q = 1) : d364289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357507, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357507, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357508 q = 1) : d364290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357508, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357508, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357509 q = 1) : d364291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357509, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357509, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100446 (p : Pattern) (ha : d308 p = 1) (hb : d357515 p = 1) : d364297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43385 q = 1) : d363996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43385, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100321 q ha hb
    | true =>
      simp only [d43385, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100324 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43386 q = 1) : d363997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43386, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43386, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357496 q = 1) : d364278 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357496, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357496, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357497 q = 1) : d364279 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357497, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357497, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357499 q = 1) : d364281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357499, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357499, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100444 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357500 q = 1) : d364282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357500, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357500, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d357501 q = 1) : d364283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357501, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357501, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d357502 q = 1) : d364284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357502, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357502, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d357503 q = 1) : d364285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357503, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357503, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d357510 q = 1) : d364292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357510, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357510, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100445 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d357511 q = 1) : d364293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357511, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357511, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d357512 q = 1) : d364294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357512, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357512, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d357513 q = 1) : d364295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357513, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357513, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d357514 q = 1) : d364296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357514, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357514, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d357515 q = 1) : d364297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357515, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357515, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100447 (p : Pattern) (ha : d308 p = 1) (hb : d357521 p = 1) : d364303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357516 q = 1) : d364298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357516, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357516, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100446 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357517 q = 1) : d364299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357517, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357517, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357518 q = 1) : d364300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357518, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357518, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357519 q = 1) : d364301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357519, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357519, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357520 q = 1) : d364302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357520, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357520, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357521 q = 1) : d364303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357521, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357521, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100448 (p : Pattern) (ha : d357556 p = 1) (hb : d363815 p = 1) : d364309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357522 q = 1) : d364304 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357522, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357522, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100447 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357523 q = 1) : d364305 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357523, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357523, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d357524 q = 1) (hb : d363813 q = 1) : d364306 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d363813, d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357524, d363813, d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d357554 q = 1) (hb : d363814 q = 1) : d364307 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d363814, d364307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357554, d363814, d364307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d357555 q = 1) (hb : d363815 q = 1) : d364308 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d363815, d364308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357555, d363815, d364308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d357556 q = 1) (hb : d363815 q = 1) : d364309 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d364309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d357556, d364309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100449 (p : Pattern) (ha : d357562 p = 1) (hb : d363815 p = 1) : d364315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d363815 q = 1) : d364310 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d364310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100448 q ha hb
    | true =>
      simp only [d357557, d364310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d363815 q = 1) : d364311 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d364311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d364311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d363815 q = 1) : d364312 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d364312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d364312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d363815 q = 1) : d364313 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d364313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d364313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d363815 q = 1) : d364314 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d364314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d364314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d363815 q = 1) : d364315 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d364315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d364315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100450 (p : Pattern) (ha : d357568 p = 1) (hb : d363819 p = 1) : d364321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d363815 q = 1) : d364316 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d364316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100449 q ha hb
    | true =>
      simp only [d357563, d364316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357564 q = 1) (hb : d363816 q = 1) : d364317 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d363816, d364317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d363816, d364317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d357565 q = 1) (hb : d363817 q = 1) : d364318 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d363817, d364318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357565, d363817, d364318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d357566 q = 1) (hb : d363818 q = 1) : d364319 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d363818, d364319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357566, d363818, d364319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d357567 q = 1) (hb : d363819 q = 1) : d364320 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d363819, d364320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357567, d363819, d364320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d357568 q = 1) (hb : d363819 q = 1) : d364321 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d364321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357568, d364321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100451 (p : Pattern) (ha : d357574 p = 1) (hb : d363819 p = 1) : d364327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d363819 q = 1) : d364322 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d364322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100450 q ha hb
    | true =>
      simp only [d357569, d364322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d363819 q = 1) : d364323 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d364323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d364323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d363819 q = 1) : d364324 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d364324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d364324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d363819 q = 1) : d364325 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d364325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d364325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d363819 q = 1) : d364326 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d364326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d364326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d363819 q = 1) : d364327 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d364327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d364327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100452 (p : Pattern) (ha : d357580 p = 1) (hb : d363819 p = 1) : d364333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d363819 q = 1) : d364328 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d364328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100451 q ha hb
    | true =>
      simp only [d357575, d364328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d363819 q = 1) : d364329 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d364329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d364329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d363819 q = 1) : d364330 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d364330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d364330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d363819 q = 1) : d364331 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d364331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d364331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d363819 q = 1) : d364332 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d364332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d364332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d363819 q = 1) : d364333 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d364333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d364333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100453 (p : Pattern) (ha : d357586 p = 1) (hb : d363819 p = 1) : d364339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d363819 q = 1) : d364334 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d364334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100452 q ha hb
    | true =>
      simp only [d357581, d364334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d363819 q = 1) : d364335 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d364335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d364335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d363819 q = 1) : d364336 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d364336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d364336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d363819 q = 1) : d364337 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d364337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d364337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d363819 q = 1) : d364338 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d364338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d364338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d363819 q = 1) : d364339 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d364339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d364339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100454 (p : Pattern) (ha : d357592 p = 1) (hb : d363819 p = 1) : d364345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d363819 q = 1) : d364340 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d364340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100453 q ha hb
    | true =>
      simp only [d357587, d364340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d363819 q = 1) : d364341 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d364341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d364341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d363819 q = 1) : d364342 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d364342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d364342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d363819 q = 1) : d364343 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d364343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d364343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d363819 q = 1) : d364344 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d364344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d364344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d363819 q = 1) : d364345 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d364345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d364345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100455 (p : Pattern) (ha : d357598 p = 1) (hb : d363819 p = 1) : d364351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d363819 q = 1) : d364346 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d364346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100454 q ha hb
    | true =>
      simp only [d357593, d364346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d363819 q = 1) : d364347 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d364347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d364347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d363819 q = 1) : d364348 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d364348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d364348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d363819 q = 1) : d364349 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d364349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d364349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d363819 q = 1) : d364350 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d364350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d364350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d363819 q = 1) : d364351 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d364351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d364351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100456 (p : Pattern) (ha : d361948 p = 1) (hb : d363985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d361937 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d361841 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
    | true =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
  have h5 (q : Pattern) (ha : d361938 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361938, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361938, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d361944 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d361945 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361945, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361945, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361946 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361946, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361946, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361947 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361947, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361947, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361948 q = 1) (hb : d363985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361948, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361948, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100457 (p : Pattern) (ha : d361969 p = 1) (hb : d363995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361937 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361841 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100390 q ha hb
    | true =>
      simp only [d361841, d363980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100391 q ha hb
  have h4 (q : Pattern) (ha : d361938 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361938, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361938, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d361944 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d361945 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361945, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361945, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d361946 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361946, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361946, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361947 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361947, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361947, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361954 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d361959 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d361961 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d361851 q = 1) (hb : d363990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100393 q ha hb
    | true =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100394 q ha hb
  have h13 (q : Pattern) (ha : d361962 q = 1) (hb : d363991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361962, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d361962, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361965 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d361966 q = 1) (hb : d363992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361966, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361966, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d361967 q = 1) (hb : d363993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361967, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d361967, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361968 q = 1) (hb : d363994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361968, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d361968, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361969 q = 1) (hb : d363995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361969, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361969, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100458 (p : Pattern) (ha : d361989 p = 1) (hb : d364280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361961 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361851 q = 1) (hb : d363990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100393 q ha hb
    | true =>
      simp only [d361851, d363990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100394 q ha hb
  have h3 (q : Pattern) (ha : d361962 q = 1) (hb : d363991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361962, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361962, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361966 q = 1) (hb : d363992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361966, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361966, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361987 q = 1) (hb : d363993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361987, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361987, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361988 q = 1) (hb : d363994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361988, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361988, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361989 q = 1) (hb : d364280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361989, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361989, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100459 (p : Pattern) (ha : d362074 p = 1) (hb : d364291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d362058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d362063 q = 1) (hb : d364286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d362063, d364286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100429 q ha hb
    | true =>
      simp only [d362063, d364286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100432 q ha hb
  have h3 (q : Pattern) (ha : d362064 q = 1) (hb : d364287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362064, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362064, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d362070 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362071 q = 1) (hb : d364288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362071, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362071, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362072 q = 1) (hb : d364289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362072, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362072, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362073 q = 1) (hb : d364290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362073, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362073, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362074 q = 1) (hb : d364291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362074, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362074, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100460 (p : Pattern) (ha : d362087 p = 1) (hb : d364297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361859 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361970 q = 1) (hb : d363996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361970, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100456 q ha hb
    | true =>
      simp only [d361970, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100457 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361983 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361984 q = 1) (hb : d363997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361984, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361984, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361985 q = 1) (hb : d364278 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361985, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361985, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361986 q = 1) (hb : d364279 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361986, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361986, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361990 q = 1) (hb : d364281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361990, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361990, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100458 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d361992 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d361993 q = 1) (hb : d364282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361993, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361993, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d361994 q = 1) (hb : d364283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361994, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361994, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d361995 q = 1) (hb : d364284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361995, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361995, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d361996 q = 1) (hb : d364285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361996, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361996, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d362075 q = 1) (hb : d364292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362075, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d362075, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100459 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d362082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d362083 q = 1) (hb : d364293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362083, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362083, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d362084 q = 1) (hb : d364294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362084, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362084, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d362085 q = 1) (hb : d364295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362085, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d362085, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d362086 q = 1) (hb : d364296 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362086, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d362086, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d362087 q = 1) (hb : d364297 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d362087, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362087, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100461 (p : Pattern) (ha : d362093 p = 1) (hb : d364303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362088 q = 1) (hb : d364298 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d362088, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362088, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100460 q ha hb
  have h2 (q : Pattern) (ha : d362089 q = 1) (hb : d364299 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d362089, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362089, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d362090 q = 1) (hb : d364300 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d362090, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362090, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d362091 q = 1) (hb : d364301 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d362091, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362091, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362092 q = 1) (hb : d364302 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d362092, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362092, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362093 q = 1) (hb : d364303 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d362093, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362093, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100462 (p : Pattern) (ha : d363867 p = 1) (hb : d364309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362094 q = 1) (hb : d364304 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d362094, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362094, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100461 q ha hb
  have h4 (q : Pattern) (ha : d362095 q = 1) (hb : d364305 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d362095, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362095, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362095 q = 1) (hb : d364306 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363865 q = 1) (hb : d364307 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d363865, d364307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363865, d364307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d363866 q = 1) (hb : d364308 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363866, d364308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363866, d364308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d363867 q = 1) (hb : d364309 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d363867, d364309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363867, d364309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro100463 (p : Pattern) (ha : d363873 p = 1) (hb : d364315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363868 q = 1) (hb : d364310 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d363868, d364310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100462 q ha hb
    | true =>
      simp only [d363868, d364310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363869 q = 1) (hb : d364311 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d363869, d364311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363869, d364311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363870 q = 1) (hb : d364312 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d363870, d364312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363870, d364312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363871 q = 1) (hb : d364313 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d363871, d364313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363871, d364313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363872 q = 1) (hb : d364314 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d363872, d364314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363872, d364314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363873 q = 1) (hb : d364315 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d363873, d364315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363873, d364315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100464 (p : Pattern) (ha : d363879 p = 1) (hb : d364321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363874 q = 1) (hb : d364316 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d363874, d364316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100463 q ha hb
    | true =>
      simp only [d363874, d364316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363875 q = 1) (hb : d364317 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d363875, d364317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363875, d364317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363876 q = 1) (hb : d364318 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d363876, d364318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363876, d364318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363877 q = 1) (hb : d364319 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d363877, d364319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363877, d364319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363878 q = 1) (hb : d364320 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d363878, d364320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363878, d364320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363879 q = 1) (hb : d364321 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d363879, d364321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363879, d364321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100465 (p : Pattern) (ha : d363885 p = 1) (hb : d364327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363880 q = 1) (hb : d364322 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d363880, d364322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100464 q ha hb
    | true =>
      simp only [d363880, d364322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363881 q = 1) (hb : d364323 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d363881, d364323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363881, d364323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363882 q = 1) (hb : d364324 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d363882, d364324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363882, d364324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363883 q = 1) (hb : d364325 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d363883, d364325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363883, d364325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363884 q = 1) (hb : d364326 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d363884, d364326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363884, d364326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363885 q = 1) (hb : d364327 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d363885, d364327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363885, d364327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100466 (p : Pattern) (ha : d363891 p = 1) (hb : d364333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363886 q = 1) (hb : d364328 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d363886, d364328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100465 q ha hb
    | true =>
      simp only [d363886, d364328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363887 q = 1) (hb : d364329 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d363887, d364329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363887, d364329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363888 q = 1) (hb : d364330 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d363888, d364330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363888, d364330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363889 q = 1) (hb : d364331 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d363889, d364331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363889, d364331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363890 q = 1) (hb : d364332 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d363890, d364332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363890, d364332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363891 q = 1) (hb : d364333 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d363891, d364333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363891, d364333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100467 (p : Pattern) (ha : d363897 p = 1) (hb : d364339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363892 q = 1) (hb : d364334 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d363892, d364334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100466 q ha hb
    | true =>
      simp only [d363892, d364334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363893 q = 1) (hb : d364335 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d363893, d364335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363893, d364335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363894 q = 1) (hb : d364336 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d363894, d364336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363894, d364336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363895 q = 1) (hb : d364337 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d363895, d364337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363895, d364337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363896 q = 1) (hb : d364338 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d363896, d364338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363896, d364338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363897 q = 1) (hb : d364339 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d363897, d364339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363897, d364339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100468 (p : Pattern) (ha : d363903 p = 1) (hb : d364345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363898 q = 1) (hb : d364340 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d363898, d364340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100467 q ha hb
    | true =>
      simp only [d363898, d364340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363899 q = 1) (hb : d364341 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d363899, d364341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363899, d364341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363900 q = 1) (hb : d364342 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d363900, d364342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363900, d364342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363901 q = 1) (hb : d364343 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d363901, d364343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363901, d364343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363902 q = 1) (hb : d364344 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d363902, d364344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363902, d364344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363903 q = 1) (hb : d364345 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d363903, d364345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363903, d364345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100469 (p : Pattern) (ha : d363909 p = 1) (hb : d364351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363904 q = 1) (hb : d364346 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d363904, d364346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100468 q ha hb
    | true =>
      simp only [d363904, d364346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363905 q = 1) (hb : d364347 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d363905, d364347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363905, d364347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363906 q = 1) (hb : d364348 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d363906, d364348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363906, d364348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363907 q = 1) (hb : d364349 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d363907, d364349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363907, d364349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363908 q = 1) (hb : d364350 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d363908, d364350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363908, d364350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363909 q = 1) (hb : d364351 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d363909, d364351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363909, d364351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100470 (p : Pattern) (ha : d363056 p = 1) (hb : d363985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d359862 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363052 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363052, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d363052, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d359937 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d363053 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363053, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363053, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d363054 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363054, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363054, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d363055 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363055, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363055, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d363056 q = 1) (hb : d363985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363056, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363056, d363985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100471 (p : Pattern) (ha : d363061 p = 1) (hb : d363995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359862 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d363980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d363052 q = 1) (hb : d363981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363052, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363052, d363981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d359937 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d363053 q = 1) (hb : d363982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363053, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363053, d363982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d363054 q = 1) (hb : d363983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363054, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363054, d363983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363055 q = 1) (hb : d363984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363055, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363055, d363984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d359947 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d359952 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d359954 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d363990 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d363057 q = 1) (hb : d363991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363057, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d363057, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d359961 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363058 q = 1) (hb : d363992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363058, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363058, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363059 q = 1) (hb : d363993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363059, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d363059, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d363060 q = 1) (hb : d363994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363060, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d363060, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d363061 q = 1) (hb : d363995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363061, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d363061, d363995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100472 (p : Pattern) (ha : d363068 p = 1) (hb : d364280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d363990 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363057 q = 1) (hb : d363991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363057, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363057, d363991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363058 q = 1) (hb : d363992 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363058, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363058, d363992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363066 q = 1) (hb : d363993 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363066, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363066, d363993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363067 q = 1) (hb : d363994 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363067, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363067, d363994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363068 q = 1) (hb : d364280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363068, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363068, d364280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100473 (p : Pattern) (ha : d363078 p = 1) (hb : d364291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d360054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d364286 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363074 q = 1) (hb : d364287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363074, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363074, d364287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d360109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363075 q = 1) (hb : d364288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363075, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363075, d364288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363076 q = 1) (hb : d364289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363076, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363076, d364289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363077 q = 1) (hb : d364290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363077, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363077, d364290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363078 q = 1) (hb : d364291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363078, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363078, d364291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100474 (p : Pattern) (ha : d363084 p = 1) (hb : d364297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363062 q = 1) (hb : d363996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363062, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100470 q ha hb
    | true =>
      simp only [d363062, d363996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100471 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363063 q = 1) (hb : d363997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363063, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363063, d363997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363064 q = 1) (hb : d364278 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363064, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363064, d364278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363065 q = 1) (hb : d364279 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363065, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363065, d364279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363069 q = 1) (hb : d364281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363069, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363069, d364281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100472 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d359988 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d363070 q = 1) (hb : d364282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363070, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363070, d364282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d363071 q = 1) (hb : d364283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363071, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d363071, d364283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d363072 q = 1) (hb : d364284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363072, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d363072, d364284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d363073 q = 1) (hb : d364285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363073, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363073, d364285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d363079 q = 1) (hb : d364292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363079, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363079, d364292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100473 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d360125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363080 q = 1) (hb : d364293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363080, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363080, d364293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363081 q = 1) (hb : d364294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363081, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d363081, d364294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d363082 q = 1) (hb : d364295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363082, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d363082, d364295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d363083 q = 1) (hb : d364296 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363083, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d363083, d364296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d363084 q = 1) (hb : d364297 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d363084, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d363084, d364297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100475 (p : Pattern) (ha : d363090 p = 1) (hb : d364303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363085 q = 1) (hb : d364298 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d363085, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363085, d364298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100474 q ha hb
  have h2 (q : Pattern) (ha : d363086 q = 1) (hb : d364299 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d363086, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363086, d364299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d363087 q = 1) (hb : d364300 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d363087, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363087, d364300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d363088 q = 1) (hb : d364301 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d363088, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363088, d364301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363089 q = 1) (hb : d364302 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d363089, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363089, d364302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363090 q = 1) (hb : d364303 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d363090, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363090, d364303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100476 (p : Pattern) (ha : d364309 p = 1) (hb : d364354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d363051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363091 q = 1) (hb : d364304 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d363091, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d363091, d364304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100475 q ha hb
  have h4 (q : Pattern) (ha : d363092 q = 1) (hb : d364305 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d363092, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363092, d364305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363092 q = 1) (hb : d364306 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d364307 q = 1) (hb : d364352 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364307, d364352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d364307, d364352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d364308 q = 1) (hb : d364353 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364308, d364353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d364308, d364353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d364309 q = 1) (hb : d364354 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364309, d364354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d364309, d364354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h8 p ha hb
theorem andIntro100477 (p : Pattern) (ha : d364315 p = 1) (hb : d364360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364310 q = 1) (hb : d364355 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364310, d364355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100476 q ha hb
    | true =>
      simp only [d364310, d364355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364311 q = 1) (hb : d364356 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364311, d364356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364311, d364356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364312 q = 1) (hb : d364357 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364312, d364357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364312, d364357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364313 q = 1) (hb : d364358 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364313, d364358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364313, d364358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364314 q = 1) (hb : d364359 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364314, d364359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364314, d364359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364315 q = 1) (hb : d364360 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364315, d364360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364315, d364360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100478 (p : Pattern) (ha : d364321 p = 1) (hb : d364366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364316 q = 1) (hb : d364361 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364316, d364361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100477 q ha hb
    | true =>
      simp only [d364316, d364361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364317 q = 1) (hb : d364362 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364317, d364362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364317, d364362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364318 q = 1) (hb : d364363 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364318, d364363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364318, d364363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364319 q = 1) (hb : d364364 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364319, d364364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364319, d364364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364320 q = 1) (hb : d364365 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364320, d364365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364320, d364365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364321 q = 1) (hb : d364366 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364321, d364366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364321, d364366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100479 (p : Pattern) (ha : d364327 p = 1) (hb : d364372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364322 q = 1) (hb : d364367 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364322, d364367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100478 q ha hb
    | true =>
      simp only [d364322, d364367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364323 q = 1) (hb : d364368 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364323, d364368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364323, d364368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364324 q = 1) (hb : d364369 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364324, d364369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364324, d364369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364325 q = 1) (hb : d364370 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364325, d364370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364325, d364370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364326 q = 1) (hb : d364371 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364326, d364371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364326, d364371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364327 q = 1) (hb : d364372 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364327, d364372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364327, d364372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100480 (p : Pattern) (ha : d364333 p = 1) (hb : d364378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364328 q = 1) (hb : d364373 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364328, d364373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100479 q ha hb
    | true =>
      simp only [d364328, d364373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364329 q = 1) (hb : d364374 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364329, d364374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364329, d364374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364330 q = 1) (hb : d364375 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364330, d364375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364330, d364375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364331 q = 1) (hb : d364376 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364331, d364376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364331, d364376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364332 q = 1) (hb : d364377 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364332, d364377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364332, d364377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364333 q = 1) (hb : d364378 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364333, d364378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364333, d364378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100481 (p : Pattern) (ha : d364339 p = 1) (hb : d364384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364334 q = 1) (hb : d364379 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364334, d364379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100480 q ha hb
    | true =>
      simp only [d364334, d364379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364335 q = 1) (hb : d364380 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364335, d364380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364335, d364380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364336 q = 1) (hb : d364381 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364336, d364381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364336, d364381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364337 q = 1) (hb : d364382 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364337, d364382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364337, d364382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364338 q = 1) (hb : d364383 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364338, d364383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364338, d364383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364339 q = 1) (hb : d364384 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364339, d364384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364339, d364384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100482 (p : Pattern) (ha : d364345 p = 1) (hb : d364390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364340 q = 1) (hb : d364385 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364340, d364385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100481 q ha hb
    | true =>
      simp only [d364340, d364385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364341 q = 1) (hb : d364386 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364341, d364386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364341, d364386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364342 q = 1) (hb : d364387 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364342, d364387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364342, d364387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364343 q = 1) (hb : d364388 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364343, d364388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364343, d364388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364344 q = 1) (hb : d364389 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364344, d364389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364344, d364389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364345 q = 1) (hb : d364390 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364345, d364390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364345, d364390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100483 (p : Pattern) (ha : d364351 p = 1) (hb : d364396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364346 q = 1) (hb : d364391 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364346, d364391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100482 q ha hb
    | true =>
      simp only [d364346, d364391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364347 q = 1) (hb : d364392 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364347, d364392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364347, d364392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364348 q = 1) (hb : d364393 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364348, d364393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364348, d364393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364349 q = 1) (hb : d364394 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364349, d364394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364349, d364394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364350 q = 1) (hb : d364395 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364350, d364395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364350, d364395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364351 q = 1) (hb : d364396 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364351, d364396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364351, d364396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100484 (p : Pattern) (ha : d308 p = 1) (hb : d42607 p = 1) : d363947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42595 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42596 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42597 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42602 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100306 q ha hb
    | true =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42603 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42604 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42605 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42606 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42366 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42367 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42368 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42607 q = 1) : d363947 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42607, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42607, d363947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100485 (p : Pattern) (ha : d308 p = 1) (hb : d42612 p = 1) : d364516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42366 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42367 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42368 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42375 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42376 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42612 q = 1) : d364516 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42612, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42612, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100486 (p : Pattern) (ha : d308 p = 1) (hb : d42620 p = 1) : d364522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42366 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42618 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42618, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42618, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42619 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42619, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42619, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42375 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42376 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42620 q = 1) : d364522 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42620, d364522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42620, d364522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100487 (p : Pattern) (ha : d308 p = 1) (hb : d42864 p = 1) : d364527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42253 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42254 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42864 q = 1) : d364527 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42864, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42864, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro100488 (p : Pattern) (ha : d308 p = 1) (hb : d42870 p = 1) : d364533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42608 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
    | true =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42609 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42610 q = 1) : d363950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42610, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42611 q = 1) : d363951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42613 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
    | true =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42614 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42615 q = 1) : d364519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42615, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42616 q = 1) : d364520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42617 q = 1) : d364521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42623 q = 1) : d364525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42624 q = 1) : d364526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42867 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42868 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42869 q = 1) : d364532 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42869, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42870 q = 1) : d364533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42870, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42870, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100489 (p : Pattern) (ha : d308 p = 1) (hb : d42369 p = 1) : d364516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42366 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42367 q = 1) : d363938 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42368 q = 1) : d363939 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42368, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42253 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42254 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42369 q = 1) : d364516 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42369, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42369, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro100490 (p : Pattern) (ha : d308 p = 1) (hb : d42873 p = 1) : d364536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42370 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
    | true =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42371 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42372 q = 1) : d364519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42372, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42373 q = 1) : d364520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42867 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42868 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42871 q = 1) : d364534 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42871, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42871, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42872 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42873 q = 1) : d364536 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42873, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42873, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100491 (p : Pattern) (ha : d308 p = 1) (hb : d42877 p = 1) : d364540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42867 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42868 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42872 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42877 q = 1) : d364540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42877, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42877, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100492 (p : Pattern) (ha : d308 p = 1) (hb : d42884 p = 1) : d364547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42874 q = 1) : d364537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100488 q ha hb
    | true =>
      simp only [d42874, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100490 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42875 q = 1) : d364538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42875, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42876 q = 1) : d364539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42876, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42878 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100490 q ha hb
    | true =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100491 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42879 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42880 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42881 q = 1) : d364544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42881, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42882 q = 1) : d364545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42882, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42883 q = 1) : d364546 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42883, d364546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42883, d364546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42884 q = 1) : d364547 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42884, d364547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42884, d364547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100493 (p : Pattern) (ha : d308 p = 1) (hb : d42888 p = 1) : d364551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42878 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100490 q ha hb
    | true =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100491 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42879 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42880 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42882 q = 1) : d364545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42882, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42887 q = 1) : d364550 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42887, d364550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42887, d364550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42888 q = 1) : d364551 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42888, d364551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42888, d364551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100494 (p : Pattern) (ha : d308 p = 1) (hb : d42894 p = 1) : d364557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42892 q = 1) : d364555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42893 q = 1) : d364556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42894 q = 1) : d364557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42894, d364557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42894, d364557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100495 (p : Pattern) (ha : d308 p = 1) (hb : d42898 p = 1) : d364561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42896 q = 1) : d364559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42897 q = 1) : d364560 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42898 q = 1) : d364561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42898, d364561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42898, d364561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100496 (p : Pattern) (ha : d308 p = 1) (hb : d42904 p = 1) : d364567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42899 q = 1) : d364562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100494 q ha hb
    | true =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100495 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42900 q = 1) : d364563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42901 q = 1) : d364564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42902 q = 1) : d364565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42903 q = 1) : d364566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42904 q = 1) : d364567 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42904, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42904, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100497 (p : Pattern) (ha : d308 p = 1) (hb : d42907 p = 1) : d364570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42892 q = 1) : d364555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42893 q = 1) : d364556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42907 q = 1) : d364570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42907, d364570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42907, d364570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100498 (p : Pattern) (ha : d308 p = 1) (hb : d42908 p = 1) : d364571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42896 q = 1) : d364559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42897 q = 1) : d364560 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42908 q = 1) : d364571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42908, d364571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42908, d364571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100499 (p : Pattern) (ha : d308 p = 1) (hb : d42914 p = 1) : d364577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42899 q = 1) : d364562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100494 q ha hb
    | true =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100495 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42900 q = 1) : d364563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42901 q = 1) : d364564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42902 q = 1) : d364565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42903 q = 1) : d364566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42909 q = 1) : d364572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100497 q ha hb
    | true =>
      simp only [d42909, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100498 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42910 q = 1) : d364573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42910, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42911 q = 1) : d364574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42911, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42912 q = 1) : d364575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42912, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42913 q = 1) : d364576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42913, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42914 q = 1) : d364577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42914, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42914, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
